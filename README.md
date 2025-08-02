# Z3 MCP Server

A Model Context Protocol (MCP) server that provides access to the Z3 Theorem Prover and constraint solver through standardized MCP tools.

## Overview

This server exposes Z3's constraint solving capabilities through MCP, allowing AI assistants and other MCP clients to solve SMT-LIB problems using the Z3 theorem prover. The server includes optional sandboxing for secure execution.

## Features

- **Z3 Integration**: Execute Z3 constraint solver on SMT-LIB input
- **Configurable Timeout**: Set custom timeout values for solver operations (default: 10 seconds)
- **Cross-Platform Sandboxing**: Run Z3 in a sandboxed environment on macOS and Linux for enhanced security
- **MCP Protocol**: Standard Model Context Protocol interface for tool integration

## Prerequisites

- Go 1.24.4 or later
- Z3 theorem prover installed on your system
- For sandboxing:
  - **macOS**: `sandbox-exec` command (built-in)
  - **Linux**: `bwrap` (bubblewrap) package

### Installing Dependencies

**Z3 Theorem Prover:**

*macOS (Homebrew):*
```bash
brew install z3
```

*Linux (Ubuntu/Debian):*
```bash
sudo apt-get install z3
```

**Sandboxing Dependencies:**

*Linux (Ubuntu/Debian):*
```bash
sudo apt-get install bubblewrap
```

*Linux (Fedora/RHEL):*
```bash
sudo dnf install bubblewrap
```

**Other platforms:**
See [Z3's official installation guide](https://github.com/Z3Prover/z3)

## Installation

1. Clone the repository:
```bash
git clone <repository-url>
cd z3-mcp
```

2. Install dependencies:
```bash
go mod download
```

3. Build the server:
```bash
go build -o z3-mcp-server
```

## Usage

### Basic Usage

Start the server on stdin/stdout (standard MCP mode):
```bash
./z3-mcp-server
```

### With Sandboxing

Enable sandboxing for enhanced security:
```bash
./z3-mcp-server -sandbox
```

The sandboxing implementation varies by platform:
- **macOS**: Uses `sandbox-exec` with the included `z3.sb` profile
- **Linux**: Uses `bubblewrap` with network isolation and read-only filesystem access

### Docker

Build and run using Docker:
```bash
docker build -t z3-mcp .
docker run -i z3-mcp
```

#### Docker with Seccomp Profile

For enhanced security, run the container with the included seccomp profile:
```bash
docker run --security-opt seccomp=./seccomp-profile.json -i z3-mcp
```

The seccomp profile is based on Docker's official default profile with all network-related syscalls removed, providing production-grade security while maintaining full container compatibility.

## MCP Tool Interface

The server provides one MCP tool:

### `z3`

Executes the Z3 constraint solver on SMT-LIB input.

**Parameters:**
- `input` (string, required): The SMT-LIB input to solve
- `timeout` (number, optional): Timeout in seconds for the Z3 solver (default: 10)

**Example SMT-LIB input:**
```smt
(declare-const x Int)
(declare-const y Int)
(assert (> x y))
(assert (= x 10))
(check-sat)
(get-model)
```

## Security Features

### Sandboxing

When enabled with the `-sandbox` flag, Z3 runs within a restricted sandbox that:
- Denies network access
- Restricts file system writes  
- Allows only necessary file reads
- Limits process execution to Z3 only
- Isolates process namespace (Linux)

**Platform-specific implementations:**
- **macOS**: Uses `sandbox-exec` with the `z3.sb` profile
- **Linux**: Uses `bubblewrap` with comprehensive filesystem and network isolation
- **Docker**: Custom seccomp profile (`seccomp-profile.json`) restricting system calls

## License

MIT License - see [LICENSE](LICENSE) file for details.

