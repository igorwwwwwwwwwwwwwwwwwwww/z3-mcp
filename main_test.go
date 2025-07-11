
package main

import (
	"context"
	"strings"
	"testing"
)

func TestSolveZ3(t *testing.T) {
	testCases := []struct {
		name          string
		input         string
		expected      string
		expectError   bool
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
			output, err := solveZ3(context.Background(), tc.input)

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
