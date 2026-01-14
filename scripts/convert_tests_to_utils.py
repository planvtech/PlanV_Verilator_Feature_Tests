#!/usr/bin/env python3
"""
Convert test files to use test_utils.svh macros.

Changes:
1. Add `include "test_utils.svh" after the header comments
2. Replace $display(...) with `DBG((...)) for debug output
3. Keep $display for error messages and important status
4. Replace $write("*-* All Finished *-*") patterns with `TEST_PASS
5. Replace $stop with `TEST_FAIL where appropriate
"""

import os
import re
import sys
from pathlib import Path

FEATURE_TESTS_DIR = Path("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests")

# Patterns that should remain as $display (only critical errors)
# Keep this list minimal - almost everything should become DBG
KEEP_DISPLAY_PATTERNS = [
    r'\*-\* All',           # Test pass/fail markers (will be converted to TEST_PASS)
]

def should_keep_display(line):
    """Check if this $display should NOT be converted to DBG."""
    # Only keep the final test marker, convert everything else to DBG
    for pattern in KEEP_DISPLAY_PATTERNS:
        if re.search(pattern, line, re.IGNORECASE):
            return True
    return False

def convert_file(filepath):
    """Convert a single test file to use test_utils.svh."""
    with open(filepath, 'r') as f:
        content = f.read()

    original_content = content
    lines = content.split('\n')
    new_lines = []
    include_added = False
    in_header = True

    for i, line in enumerate(lines):
        # Add include after header comments
        if in_header and not line.strip().startswith('//') and line.strip() != '':
            # Check if include already exists
            if '`include "test_utils.svh"' not in content:
                new_lines.append('`include "test_utils.svh"')
                new_lines.append('')
                include_added = True
            in_header = False

        # Convert $write("*-* All Finished *-*"\n); $finish; to `TEST_PASS
        if re.search(r'\$write\s*\(\s*"\*-\*\s*All\s*Finished\s*\*-\*', line):
            # Check if next line has $finish
            if i + 1 < len(lines) and '$finish' in lines[i + 1]:
                new_lines.append(line.replace(re.search(r'\$write\s*\([^)]+\)\s*;', line).group(), '`TEST_PASS'))
                continue
            else:
                new_lines.append(re.sub(r'\$write\s*\(\s*"\*-\*\s*All\s*Finished\s*\*-\*[^"]*"\s*\)\s*;', '`TEST_PASS', line))
                continue

        # Skip $finish if it follows TEST_PASS pattern (already handled)
        if '$finish' in line and i > 0:
            prev_line = lines[i-1] if i > 0 else ''
            if 'TEST_PASS' in new_lines[-1] if new_lines else False:
                continue
            if re.search(r'\*-\*\s*All\s*Finished', prev_line):
                continue

        # Convert $display to `DBG for debug output (not error messages)
        if '$display' in line and not should_keep_display(line):
            # Match $display("...", args); on single line
            match = re.search(r'\$display\s*\(([^;]+)\)\s*;', line)
            if match:
                args = match.group(1).strip()
                # Convert to `DBG((...))
                new_line = line.replace(match.group(0), f'`DBG(({args}))')
                new_lines.append(new_line)
                continue
            else:
                # Multi-line $display - just replace $display with `DBG(
                new_line = re.sub(r'\$display\s*\(', '`DBG((', line)
                new_lines.append(new_line)
                continue

        # Handle continuation of multi-line $display - add extra ) before ;
        if new_lines and '`DBG((' in new_lines[-1] and ';' not in new_lines[-1]:
            if ';' in line:
                # End of multi-line, add closing paren
                new_line = line.replace(');', '))')
                new_lines.append(new_line)
                continue

        new_lines.append(line)

    new_content = '\n'.join(new_lines)

    # Only write if content changed
    if new_content != original_content:
        with open(filepath, 'w') as f:
            f.write(new_content)
        return True
    return False

def main():
    """Main entry point."""
    test_files = list(FEATURE_TESTS_DIR.rglob("*.sv"))
    # Exclude archived files
    test_files = [f for f in test_files if '_archived' not in str(f)]

    print(f"Found {len(test_files)} test files")

    converted = 0
    skipped = 0
    errors = []

    for filepath in sorted(test_files):
        try:
            if convert_file(filepath):
                print(f"  [CONVERTED] {filepath.relative_to(FEATURE_TESTS_DIR)}")
                converted += 1
            else:
                print(f"  [SKIPPED]   {filepath.relative_to(FEATURE_TESTS_DIR)}")
                skipped += 1
        except Exception as e:
            print(f"  [ERROR]     {filepath.relative_to(FEATURE_TESTS_DIR)}: {e}")
            errors.append((filepath, e))

    print()
    print(f"Summary:")
    print(f"  Converted: {converted}")
    print(f"  Skipped:   {skipped}")
    print(f"  Errors:    {len(errors)}")

    if errors:
        print("\nErrors:")
        for filepath, e in errors:
            print(f"  {filepath}: {e}")

if __name__ == "__main__":
    main()
