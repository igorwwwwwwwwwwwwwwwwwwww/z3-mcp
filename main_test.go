package main

import (
	"context"
	"os"
	"os/exec"
	"runtime"
	"strings"
	"testing"
)

func TestSandbox(t *testing.T) {
	switch runtime.GOOS {
	case "darwin":
		testMacOSSandbox(t)
	case "linux":
		testLinuxSandbox(t)
	default:
		t.Skipf("sandbox testing not implemented for %s", runtime.GOOS)
	}
}

func testMacOSSandbox(t *testing.T) {
	// Check if sandbox-exec is available
	if _, err := exec.LookPath("sandbox-exec"); err != nil {
		t.Skip("sandbox-exec not available")
	}

	// Test with the actual z3.sb profile - network should be denied
	cmd := exec.CommandContext(context.Background(), "sandbox-exec", "-f", "z3.sb", "ping", "-c1", "8.8.8.8")
	output, err := cmd.CombinedOutput()
	if err == nil {
		t.Errorf("expected network to be denied, but ping succeeded. output: %q", output)
	}
}

func testLinuxSandbox(t *testing.T) {
	// Check if bwrap is available
	if _, err := exec.LookPath("bwrap"); err != nil {
		t.Skip("bwrap (bubblewrap) not available")
	}

	// Test network isolation - ping should fail
	cmd := exec.CommandContext(context.Background(), "bwrap",
		"--ro-bind", "/usr", "/usr",
		"--ro-bind", "/lib", "/lib",
		"--ro-bind", "/bin", "/bin",
		"--tmpfs", "/tmp",
		"--proc", "/proc",
		"--dev", "/dev",
		"--unshare-net",
		"--die-with-parent",
		"ping", "-c1", "8.8.8.8")
	output, err := cmd.CombinedOutput()
	if err == nil {
		t.Errorf("expected network to be denied, but ping succeeded. output: %q", output)
	}
}

func TestSolveZ3(t *testing.T) {
	testCases := []struct {
		name          string
		input         string
		expected      string
		expectError   bool
		sandbox       bool // Add a sandbox flag to the test cases
	}{
		{
			name: "Satisfiable",
			input: `(declare-const p Bool)
(assert p)
(check-sat)`,
			expected: "sat",
			expectError: false,
		},
		{
			name: "Unsatisfiable",
			input: `(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)`,
			expected: "unsat",
			expectError: false,
		},
		{
			name: "Invalid Input",
			input: `(declare-const p Bool)
(invalid-command)`,
			expected: "error", // We expect an error message from Z3
			expectError: true,
		},
		{
			name: "Complex Satisfiable",
			input: `(declare-const x Int)
(declare-const y Int)
(assert (> x y))
(assert (= x 10))
(check-sat)`,
			expected: "sat",
			expectError: false,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			output, err := solveZ3(context.Background(), tc.input, tc.sandbox)

			if tc.expectError {
				if err == nil {
					t.Errorf("expected an error, but got none. output: %q", output)
				} else if !strings.Contains(err.Error(), tc.expected) {
					t.Errorf("expected error to contain %q, but got %q", tc.expected, err.Error())
				}
			} else {
				if err != nil {
					t.Fatalf("unexpected error: %v", err)
				}
				if !strings.Contains(output, tc.expected) {
					t.Errorf("expected output to contain %q, but got %q", tc.expected, output)
				}
			}
		})
	}
}