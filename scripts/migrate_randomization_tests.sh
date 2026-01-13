#!/usr/bin/env bash
# DESCRIPTION: Migrate randomization tests to new directory structure
#
# Usage: ./scripts/migrate_randomization_tests.sh [--dry-run]
#
# This script:
# 1. Reads MIGRATION_MAP.csv
# 2. Renames and moves test files
# 3. Updates module names in files
# 4. Creates migration log
# 5. Archives old structure

set -e

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$PROJECT_ROOT"

# Flags
DRY_RUN=0
if [[ "$1" == "--dry-run" ]]; then
    DRY_RUN=1
    echo "=== DRY RUN MODE - No files will be modified ==="
fi

# Paths
MIGRATION_MAP="MIGRATION_MAP.csv"
MIGRATION_LOG="MIGRATION_LOG_$(date +%Y%m%d_%H%M%S).txt"
OLD_ROOT="planv_tests/feature_tests/constrained_random"
NEW_ROOT="planv_tests/feature_tests/randomization"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
TOTAL=0
RENAMED=0
MOVED=0
SKIPPED=0
ERRORS=0

log() {
    echo -e "${BLUE}[INFO]${NC} $*" | tee -a "$MIGRATION_LOG"
}

warn() {
    echo -e "${YELLOW}[WARN]${NC} $*" | tee -a "$MIGRATION_LOG"
}

error() {
    echo -e "${RED}[ERROR]${NC} $*" | tee -a "$MIGRATION_LOG"
    ((ERRORS++))
}

success() {
    echo -e "${GREEN}[OK]${NC} $*" | tee -a "$MIGRATION_LOG"
}

# Function to update module name in file
update_module_name() {
    local file="$1"
    local old_module="$2"
    local new_module="$3"

    if [[ $DRY_RUN -eq 1 ]]; then
        log "Would update module name: $old_module -> $new_module in $file"
        return 0
    fi

    # Extract old module name from file if not provided
    if [[ -z "$old_module" ]]; then
        old_module=$(grep -m1 "^module " "$file" | sed 's/module //; s/[; ].*$//')
    fi

    if [[ -z "$old_module" ]]; then
        warn "Could not find module declaration in $file"
        return 1
    fi

    # Update module name
    sed -i "s/^module ${old_module}/module ${new_module}/" "$file"
    log "Updated module name: $old_module -> $new_module"
    return 0
}

# Function to migrate a single file
migrate_file() {
    local orig_path="$1"
    local new_dir="$2"
    local new_filename="$3"
    local action="$4"

    ((TOTAL++))

    # Check if source file exists
    if [[ ! -f "$orig_path" ]]; then
        warn "Source file not found: $orig_path"
        ((SKIPPED++))
        return 1
    fi

    # Prepare destination
    local dest_file="$new_dir/$new_filename"

    # Extract module names from filenames
    local old_module=$(basename "$orig_path" .sv)
    local new_module=$(basename "$new_filename" .sv)

    log "Processing: $orig_path"
    log "  Action: $action"
    log "  Destination: $dest_file"
    log "  Module: $old_module -> $new_module"

    if [[ $DRY_RUN -eq 1 ]]; then
        success "Would migrate: $orig_path -> $dest_file"
        return 0
    fi

    # Create destination directory
    mkdir -p "$new_dir"

    # Copy file to temp location
    local temp_file=$(mktemp)
    cp "$orig_path" "$temp_file"

    # Update module name if needed
    if [[ "$old_module" != "$new_module" ]]; then
        if ! update_module_name "$temp_file" "$old_module" "$new_module"; then
            error "Failed to update module name in $orig_path"
            rm "$temp_file"
            return 1
        fi
        ((RENAMED++))
    fi

    # Move to destination
    mv "$temp_file" "$dest_file"

    # Move original to archive (don't delete yet)
    local archive_dir="_archived/20250112_pre_refactor/$(dirname "$orig_path")"
    mkdir -p "$archive_dir"
    cp "$orig_path" "$archive_dir/"

    ((MOVED++))
    success "Migrated: $orig_path -> $dest_file"
    return 0
}

# Main migration logic
main() {
    log "=== Randomization Tests Migration Started ==="
    log "Date: $(date)"
    log "Project root: $PROJECT_ROOT"

    # Verify migration map exists
    if [[ ! -f "$MIGRATION_MAP" ]]; then
        error "Migration map not found: $MIGRATION_MAP"
        exit 1
    fi

    # Read CSV and process each line
    local line_num=0
    while IFS=',' read -r orig_path new_path new_filename ieee_section action priority notes; do
        ((line_num++))

        # Skip header and comment lines
        if [[ $line_num -eq 1 ]] || [[ "$orig_path" =~ ^# ]]; then
            continue
        fi

        # Skip empty lines
        if [[ -z "$orig_path" ]]; then
            continue
        fi

        # Skip lines that need manual analysis
        if [[ "$action" == "ANALYZE_DUPLICATE" ]] || [[ "$action" == "ARCHIVE" ]]; then
            log "Skipping (action=$action): $orig_path"
            ((SKIPPED++))
            continue
        fi

        # Skip TBD entries
        if [[ "$new_path" == "TBD" ]]; then
            log "Skipping (TBD): $orig_path"
            ((SKIPPED++))
            continue
        fi

        # Migrate the file
        if ! migrate_file "$orig_path" "$new_path" "$new_filename" "$action"; then
            error "Failed to migrate: $orig_path"
        fi

    done < "$MIGRATION_MAP"

    # Summary
    log ""
    log "=== Migration Summary ==="
    log "Total entries processed: $TOTAL"
    log "Files renamed: $RENAMED"
    log "Files moved: $MOVED"
    log "Files skipped: $SKIPPED"
    log "Errors: $ERRORS"

    if [[ $ERRORS -eq 0 ]]; then
        success "Migration completed successfully!"
    else
        error "Migration completed with $ERRORS errors"
        exit 1
    fi

    # Next steps
    log ""
    log "=== Next Steps ==="
    log "1. Review migration log: $MIGRATION_LOG"
    log "2. Run tests to verify: ./scripts/run -b master -t $NEW_ROOT"
    log "3. Check for duplicates: ./scripts/detect_duplicates.sh"
    log "4. Review archived files: _archived/20250112_pre_refactor/"
    log "5. If all looks good, commit changes: git add . && git commit"
}

# Run main
main
