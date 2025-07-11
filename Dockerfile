
# Use the official Go image as a parent image
FROM golang:1.22-alpine

# Set the working directory in the container
WORKDIR /app

# Install Z3
RUN apk add --no-cache z3

# Copy the Go module files
COPY go.mod go.sum ./

# Download the Go module dependencies
RUN go mod download

# Copy the source code
COPY . .

# Build the Go application
RUN go build -o /z3-mcp-server

# Expose the port the server runs on
EXPOSE 8080

# Run the executable
ENTRYPOINT ["/z3-mcp-server"]
