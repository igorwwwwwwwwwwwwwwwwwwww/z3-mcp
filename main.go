package main

import (
	"context"
	"fmt"
	"io"
	"log"
	"os/exec"
	"strings"
	"time"

	"github.com/mark3labs/mcp-go/mcp"
	"github.com/mark3labs/mcp-go/server"
)

// solveZ3 takes SMT-LIB input as a string, executes Z3, and returns the output.
func solveZ3(ctx context.Context, input string) (string, error) {
	// Execute Z3, passing "-in" to read from stdin
	cmd := exec.CommandContext(ctx, "z3", "-in")

	// Pipe the input to the command's stdin
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return "", fmt.Errorf("failed to create stdin pipe: %w", err)
	}

	go func() {
		defer stdin.Close()
		io.WriteString(stdin, input)
	}()

	// Run the command and capture the output
	output, err := cmd.CombinedOutput()
	if err != nil {
		return "", fmt.Errorf("error executing Z3: %w %s", err, output)
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

	var timeoutVal int64 = 10 // Default timeout
	if timeoutArg, ok := args["timeout"]; ok {
		if tv, ok := timeoutArg.(int64); ok {
			timeoutVal = tv
		} else if tv, ok := timeoutArg.(float64); ok {
			timeoutVal = int64(tv)
		}
	}

	timeout := time.Duration(timeoutVal) * time.Second
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

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
		mcp.WithNumber("timeout",
			mcp.Description("Timeout in seconds for the Z3 solver."),
			mcp.DefaultNumber(10),
		),
	), z3Tool)

	log.Println("Starting Z3 MCP server on stdin/stdout")
	if err := server.ServeStdio(mcpServer); err != nil {
		log.Fatalf("Server error: %v", err)
	}
}