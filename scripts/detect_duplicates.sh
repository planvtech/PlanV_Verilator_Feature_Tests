#!/usr/bin/env bash
# DESCRIPTION: Detect duplicate test files based on content
#
# Usage: ./scripts/detect_duplicates.sh [directory]
#
# This script:
# 1. Computes MD5 hashes of all .sv files
# 2. Identifies exact duplicates
# 3. Performs fuzzy comparison (ignoring comments/whitespace)
# 4. Generates duplicate report

set -e

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Target directory (default: constrained_random)
TARGET_DIR="${1:-planv_tests/feature_tests/constrained_random}"
cd "$PROJECT_ROOT"

if [[ ! -d "$TARGET_DIR" ]]; then
    echo "Error: Directory not found: $TARGET_DIR"
    exit 1
fi

# Output files
REPORT="DUPLICATE_REPORT_$(date +%Y%m%d_%H%M%S).md"
EXACT_DUPS="exact_duplicates.tmp"
FUZZY_DUPS="fuzzy_duplicates.tmp"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log() {
    echo -e "${BLUE}[INFO]${NC} $*"
}

warn() {
    echo -e "${YELLOW}[WARN]${NC} $*"
}

success() {
    echo -e "${GREEN}[OK]${NC} $*"
}

# Initialize report
cat > "$REPORT" <<EOF
# Duplicate Test Files Report

Generated: $(date)
Directory: $TARGET_DIR

## Summary

EOF

log "Scanning directory: $TARGET_DIR"

# Find all .sv files
TOTAL_FILES=$(find "$TARGET_DIR" -name "*.sv" -type f | wc -l)
log "Found $TOTAL_FILES test files"

# Exact duplicate detection (MD5 hash)
log "Computing MD5 hashes..."
find "$TARGET_DIR" -name "*.sv" -type f -exec md5sum {} \; | sort > "$EXACT_DUPS"

# Find duplicates
EXACT_DUP_GROUPS=$(awk '{print $1}' "$EXACT_DUPS" | uniq -d | wc -l)
EXACT_DUP_FILES=$(awk '{print $1}' "$EXACT_DUPS" | uniq -d | while read hash; do
    grep "^$hash" "$EXACT_DUPS" | wc -l
done | awk '{sum+=$1} END {print sum}')

cat >> "$REPORT" <<EOF
- Total files scanned: $TOTAL_FILES
- Exact duplicate groups: $EXACT_DUP_GROUPS
- Files involved in exact duplication: $EXACT_DUP_FILES

## Exact Duplicates

Files with identical content (same MD5 hash):

EOF

if [[ $EXACT_DUP_GROUPS -gt 0 ]]; then
    log "Found $EXACT_DUP_GROUPS exact duplicate groups"

    awk '{print $1}' "$EXACT_DUPS" | uniq -d | while read hash; do
        echo "" >> "$REPORT"
        echo "### Group: $hash" >> "$REPORT"
        echo "" >> "$REPORT"
        echo '```' >> "$REPORT"
        grep "^$hash" "$EXACT_DUPS" | awk '{print $2}' >> "$REPORT"
        echo '```' >> "$REPORT"
        echo "" >> "$REPORT"
        echo "**Action**: Keep one, archive others" >> "$REPORT"
        echo "" >> "$REPORT"
    done
else
    echo "No exact duplicates found." >> "$REPORT"
    success "No exact duplicates detected"
fi

# Fuzzy duplicate detection (ignore comments and whitespace)
log "Performing fuzzy comparison..."

cat >> "$REPORT" <<EOF

## Fuzzy Duplicates

Files with similar content (ignoring comments, whitespace, and module names):

EOF

# Create normalized versions of files
NORM_DIR=$(mktemp -d)
find "$TARGET_DIR" -name "*.sv" -type f | while read file; do
    # Normalize: remove comments, collapse whitespace, remove module name differences
    norm_file="$NORM_DIR/$(echo "$file" | md5sum | awk '{print $1}').norm"
    sed -e 's://.*$::' \
        -e '/^\/\*/,/\*\//d' \
        -e 's/module [a-zA-Z0-9_]*/module XXX/' \
        -e 's/[[:space:]]\+/ /g' \
        -e '/^[[:space:]]*$/d' \
        "$file" | tr -d ' \t\n' > "$norm_file"
    echo "$file" > "$norm_file.path"
done

# Find duplicates in normalized files
cd "$NORM_DIR"
md5sum *.norm | sort > normalized_hashes.txt
FUZZY_DUP_GROUPS=$(awk '{print $1}' normalized_hashes.txt | uniq -d | wc -l)
cd "$PROJECT_ROOT"

if [[ $FUZZY_DUP_GROUPS -gt 0 ]]; then
    log "Found $FUZZY_DUP_GROUPS fuzzy duplicate groups"

    cd "$NORM_DIR"
    awk '{print $1}' normalized_hashes.txt | uniq -d | while read hash; do
        echo "" >> "$PROJECT_ROOT/$REPORT"
        echo "### Fuzzy Group: $hash" >> "$PROJECT_ROOT/$REPORT"
        echo "" >> "$PROJECT_ROOT/$REPORT"
        echo '```' >> "$PROJECT_ROOT/$REPORT"
        grep "^$hash" normalized_hashes.txt | awk '{print $2}' | while read norm_file; do
            cat "$norm_file.path" >> "$PROJECT_ROOT/$REPORT"
        done
        echo '```' >> "$PROJECT_ROOT/$REPORT"
        echo "" >> "$PROJECT_ROOT/$REPORT"
        echo "**Action**: Review manually - may differ only in module names or comments" >> "$PROJECT_ROOT/$REPORT"
        echo "" >> "$PROJECT_ROOT/$REPORT"
    done
    cd "$PROJECT_ROOT"
else
    echo "No fuzzy duplicates found." >> "$REPORT"
    success "No fuzzy duplicates detected"
fi

# Cleanup
rm -rf "$NORM_DIR" "$EXACT_DUPS"

# File name similarity check
log "Checking for similar filenames..."

cat >> "$REPORT" <<EOF

## Similar Filenames

Files with similar names that might be duplicates:

EOF

find "$TARGET_DIR" -name "*.sv" -type f | sed 's:.*/::' | sort | while read filename; do
    basename="${filename%.sv}"
    # Look for similar names (e.g., t_foo, t_foo_v1, t_foo_test)
    similar=$(find "$TARGET_DIR" -name "*.sv" -type f | sed 's:.*/::' | grep -E "${basename%_*}" | grep -v "^$filename$" || true)
    if [[ -n "$similar" ]]; then
        echo "" >> "$REPORT"
        echo "### Similar to: $filename" >> "$REPORT"
        echo '```' >> "$REPORT"
        echo "$filename" >> "$REPORT"
        echo "$similar" >> "$REPORT"
        echo '```' >> "$REPORT"
        echo "**Action**: Review manually - may be variants or duplicates" >> "$REPORT"
    fi
done

# Summary statistics
cat >> "$REPORT" <<EOF

## Recommendations

1. **Exact duplicates**:
   - Keep the file in the most appropriate location
   - Archive others to \`_archived/20250112_pre_refactor/duplicates/\`
   - Document the decision

2. **Fuzzy duplicates**:
   - Compare files manually (use \`diff\` or \`vimdiff\`)
   - If functionally identical, keep one
   - If they test different aspects, rename to clarify difference

3. **Similar filenames**:
   - Check if they're variants (v1, v2) of same test
   - Consider merging into one comprehensive test
   - Or clearly differentiate with better naming

## Next Steps

1. Review this report: $REPORT
2. Make decisions on which files to keep
3. Update MIGRATION_MAP.csv accordingly
4. Run migration script

EOF

success "Duplicate detection complete"
log "Report generated: $REPORT"

# Print summary to console
echo ""
echo "=== Duplicate Detection Summary ==="
echo "Total files: $TOTAL_FILES"
echo "Exact duplicate groups: $EXACT_DUP_GROUPS"
echo "Fuzzy duplicate groups: $FUZZY_DUP_GROUPS"
echo ""
echo "Full report: $REPORT"
