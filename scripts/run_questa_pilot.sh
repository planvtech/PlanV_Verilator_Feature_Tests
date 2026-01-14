#!/bin/bash
# DESCRIPTION: Pilot QuestaSim test runner for a single directory
#
# Usage: ./run_questa_pilot.sh <relative_test_dir>
# Example: ./run_questa_pilot.sh 19_functional_coverage/bins

set -e

# Configuration
FEATURE_TESTS_DIR="/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests"
SIM_DIR="/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/sim/feature_tests"
REPORT_DIR="/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/reports"

# Color codes (terminal only)
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Helper function: output to both terminal (with color) and log (plain text)
log_msg() {
    local msg="$1"
    echo -e "$msg"
    echo -e "$msg" | sed 's/\x1b\[[0-9;]*m//g' >> "${PILOT_LOG}"
}

log_msg_n() {
    local msg="$1"
    echo -n -e "$msg"
    echo -n -e "$msg" | sed 's/\x1b\[[0-9;]*m//g' >> "${PILOT_LOG}"
}

# Check arguments
if [ $# -lt 1 ]; then
    echo "Usage: $0 <relative_test_dir>"
    echo "Example: $0 19_functional_coverage/bins"
    echo ""
    echo "Available directories:"
    find "${FEATURE_TESTS_DIR}" -type d ! -path "*/_archived/*" -mindepth 1 | sed "s|${FEATURE_TESTS_DIR}/||" | sort
    exit 1
fi

TEST_SUBDIR=$1
TARGET_DIR="${FEATURE_TESTS_DIR}/${TEST_SUBDIR}"

if [ ! -d "${TARGET_DIR}" ]; then
    echo "Error: Directory not found: ${TARGET_DIR}"
    exit 1
fi

# Test counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

# Create report directory
mkdir -p "${REPORT_DIR}"

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
PILOT_LOG="${REPORT_DIR}/pilot_${TEST_SUBDIR//\//_}_${TIMESTAMP}.log"

# Initialize log file
echo "==============================================================" > "${PILOT_LOG}"
echo "=============================================================="
log_msg "QuestaSim Pilot Test - ${TEST_SUBDIR}"
log_msg "Time: $(date)"
log_msg "=============================================================="
log_msg ""

# Function to check test result
check_test_result() {
    local log_file=$1

    if [ ! -f "${log_file}" ]; then
        return 2
    fi

    if grep -q "\*-\* All Tests Passed \*-\*" "${log_file}" || \
       grep -q "\*-\* All Finished \*-\*" "${log_file}"; then
        return 0
    fi

    return 1
}

# Function to check if test is a negative test (expected to fail compilation)
# Supports two detection methods:
#   1. Path contains "/invalid/" directory
#   2. File contains "// TEST_NEGATIVE:" comment
is_negative_test() {
    local test_path=$1
    # Method 1: Path-based detection
    if [[ "${test_path}" == *"/invalid/"* ]]; then
        return 0
    fi
    # Method 2: Comment-based detection
    if grep -q "^// TEST_NEGATIVE:" "${test_path}" 2>/dev/null; then
        return 0
    fi
    return 1
}

# Counters for negative tests
EXPECTED_FAIL_TESTS=0

# Function to run a single test
run_test() {
    local test_path=$1
    local test_name=$(basename "${test_path}" .sv)
    local test_dir=$(dirname "${test_path}")
    local relative_path=${test_dir#${FEATURE_TESTS_DIR}/}

    # Check if this is a negative test
    local negative_test=0
    if is_negative_test "${test_path}"; then
        negative_test=1
    fi

    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    if [ ${negative_test} -eq 1 ]; then
        log_msg "${BLUE}[TEST ${TOTAL_TESTS}]${NC} ${test_name} (negative test)"
    else
        log_msg "${BLUE}[TEST ${TOTAL_TESTS}]${NC} ${test_name}"
    fi

    # Create simulation directory
    local sim_test_dir="${SIM_DIR}/${relative_path}/${test_name}"
    mkdir -p "${sim_test_dir}"

    cd "${sim_test_dir}"

    # Create work library
    if [ ! -d "work" ]; then
        vlib work >> "${PILOT_LOG}" 2>&1 || true
    fi

    # Compile (with include path for common utilities)
    local common_dir="/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/common"
    log_msg_n "  Compiling..."
    local compile_result=0
    if vlog +incdir+${common_dir} "${test_path}" >> "${PILOT_LOG}" 2>&1; then
        log_msg " done"
    else
        compile_result=1
        log_msg " failed"
    fi

    # Handle negative tests (expected compilation failure)
    if [ ${negative_test} -eq 1 ]; then
        if [ ${compile_result} -eq 1 ]; then
            # Negative test failed compilation as expected
            log_msg "  ${YELLOW}✓ XFAIL${NC} (expected compilation failure)"
            PASSED_TESTS=$((PASSED_TESTS + 1))
            EXPECTED_FAIL_TESTS=$((EXPECTED_FAIL_TESTS + 1))
        else
            # Negative test compiled successfully when it should have failed
            log_msg "  ${RED}✗ FAIL${NC} (expected compilation failure but compiled)"
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
        log_msg ""
        return
    fi

    # Normal test - compilation failure is a real failure
    if [ ${compile_result} -eq 1 ]; then
        log_msg "  ${RED}✗ COMPILATION FAILED${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        log_msg ""
        return
    fi

    # Simulate
    log_msg_n "  Simulating..."
    if vsim -voptargs="+acc" "${test_name}" -c -do "log -r /*; run -all; quit" -l "${test_name}.log" >> "${PILOT_LOG}" 2>&1; then
        log_msg " done"
    else
        log_msg ""
        log_msg "  ${RED}✗ SIMULATION FAILED${NC}"
        ((FAILED_TESTS++))
        log_msg ""
        return
    fi

    # Check result
    if check_test_result "${test_name}.log"; then
        log_msg "  ${GREEN}✓ PASS${NC}"
        ((PASSED_TESTS++))
    else
        log_msg "  ${RED}✗ FAIL (output verification)${NC}"
        ((FAILED_TESTS++))

        # Show last few lines of log for debugging
        log_msg "  Last 10 lines of simulation log:"
        tail -10 "${test_name}.log" | sed 's/^/    /' >> "${PILOT_LOG}"
        tail -10 "${test_name}.log" | sed 's/^/    /'
    fi

    log_msg ""
}

# Find and run tests
log_msg "Searching for tests in: ${TARGET_DIR}"
log_msg ""

# Temporarily disable exit on error for test loop
set +e

while IFS= read -r test_file; do
    run_test "${test_file}"
done < <(find "${TARGET_DIR}" -type f -name "*.sv" | sort)

# Re-enable exit on error
set -e

# Summary
log_msg "=============================================================="
log_msg "Pilot Test Summary"
log_msg "=============================================================="
log_msg "Directory: ${TEST_SUBDIR}"
log_msg "Total Tests:   ${TOTAL_TESTS}"
log_msg "Passed:        ${PASSED_TESTS}"
if [ ${EXPECTED_FAIL_TESTS} -gt 0 ]; then
    log_msg "  (includes ${EXPECTED_FAIL_TESTS} expected failures)"
fi
log_msg "Failed:        ${FAILED_TESTS}"

if [ ${TOTAL_TESTS} -gt 0 ]; then
    PASS_RATE=$((PASSED_TESTS * 100 / TOTAL_TESTS))
    log_msg "Pass Rate:     ${PASS_RATE}%"
fi

log_msg ""
log_msg "Log saved to: ${PILOT_LOG}"
log_msg "=============================================================="

# Exit status
if [ ${FAILED_TESTS} -gt 0 ]; then
    exit 1
else
    exit 0
fi
