package main

import (
	"context"
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"os/exec"
	"strings"

	"github.com/mark3labs/mcp-go/mcp"
	"github.com/mark3labs/mcp-go/server"
)

// solveZ3 takes SMT-LIB input as a string, executes Z3, and returns the output.
func solveZ3(ctx context.Context, input string) (string, error) {
	// Create a temporary file to store the SMT-LIB input
	tmpfile, err := ioutil.TempFile("", "smtlib_input_*.smt2")
	if err != nil {
		return "", fmt.Errorf("failed to create temporary file: %w", err)
	}
	defer os.Remove(tmpfile.Name()) // Clean up the file

	if _, err := tmpfile.WriteString(input); err != nil {
		return "", fmt.Errorf("failed to write to temporary file: %w", err)
	}
	if err := tmpfile.Close(); err != nil {
		return "", fmt.Errorf("failed to close temporary file: %w", err)
	}

	// Execute Z3
	cmd := exec.CommandContext(ctx, "z3", tmpfile.Name())
	output, err := cmd.CombinedOutput()
	if err != nil {
		return "", fmt.Errorf("error executing Z3: %w\n%s", err, output)
	}

	// Z3 sometimes prints errors to stdout but exits with code 0.
	if strings.Contains(string(output), "unsupported") {
		return "", fmt.Errorf("z3 reported an error: %s", string(output))
	}

	return string(output), nil
}

func z3Tool(ctx context.Context, request mcp.CallToolRequest) (*mcp.CallToolResult, error) {
	args := request.GetArguments()
	input, ok := args["input"].(string)
	if !ok {
		return nil, fmt.Errorf("invalid 'input' argument")
	}

	output, err := solveZ3(ctx, input)
	if err != nil {
		return nil, err
	}

	return &mcp.CallToolResult{
		Content: []mcp.Content{
			mcp.TextContent{
				Type: "text",
				Text: output,
			},
		},
	}, nil
}

func main() {
	mcpServer := server.NewMCPServer("z3-mcp", "0.1.0")

	mcpServer.AddTool(mcp.NewTool("z3",
		mcp.WithDescription("Run the Z3 constraint solver on SMT-LIB input"),
		mcp.WithString("input",
			mcp.Description("The SMT-LIB input to solve"),
			mcp.Required(),
		),
	), z3Tool)

	log.Println("Starting Z3 MCP server on stdin/stdout")
	if err := server.ServeStdio(mcpServer); err != nil {
		log.Fatalf("Server error: %v", err)
	}
}