#!/usr/bin/env python3
import sys

def check_range(lean_file: str, start: int, end: int, context: int = 30):
    with open(lean_file, "rb") as f:
        content = f.read()
    
    # Get context before
    ctx_start = max(0, start - context)
    before = content[ctx_start:start].decode("utf-8", errors="replace")
    
    # Get the range content
    text = content[start:end].decode("utf-8", errors="replace")
    
    # Get context after
    ctx_end = min(len(content), end + context)
    after = content[end:ctx_end].decode("utf-8", errors="replace")
    
    print(f"File: {lean_file}")
    print(f"Range: [{start}, {end}] ({end - start} bytes)")
    print()
    print(f"Before ({context} chars): {repr(before)}")
    print(f"After  ({context} chars): {repr(after)}")
    print()
    print("--- Content ---")
    print(text)
    print("--- End ---")

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print("Usage: python check_range.py <lean_file> <start> <end> [context]")
        print("Example: python check_range.py /path/to/file.lean 10940 13645")
        sys.exit(1)
    
    lean_file = sys.argv[1]
    start = int(sys.argv[2])
    end = int(sys.argv[3])
    context = int(sys.argv[4]) if len(sys.argv) > 4 else 30
    
    check_range(lean_file, start, end, context)

