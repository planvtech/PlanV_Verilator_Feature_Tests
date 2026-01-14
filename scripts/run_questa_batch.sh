#!/bin/bash
# DESCRIPTION: Batch QuestaSim runner for PlanV Verilator Feature Tests
#
# This script compiles and simulates all feature tests using QuestaSim (vsim)
# and generates a comprehensive test report.

# Don't exit on error - we want to run all tests even if some fail
# set -e

# Configuration
FEATURE_TESTS_DIR="/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests"
SIM_DIR="/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/sim/feature_tests"
REPORT_DIR="/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/reports"
COMMON_DIR="/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/common"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
SUMMARY_FILE="${REPORT_DIR}/questa_summary_${TIMESTAMP}.txt"
DETAILED_LOG="${REPORT_DIR}/questa_detailed_${TIMESTAMP}.log"

# Color codes for terminal output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Test counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
SKIPPED_TESTS=0
EXPECTED_FAIL_TESTS=0

# Arrays to track test results
declare -a FAILED_TEST_LIST
declare -a SKIPPED_TEST_LIST
declare -a EXPECTED_FAIL_LIST

# Create report directory
mkdir -p "${REPORT_DIR}"

# Initialize report files
echo "==============================================================" > "${SUMMARY_FILE}"
echo "QuestaSim Feature Test Report" >> "${SUMMARY_FILE}"
echo "Generated: $(date)" >> "${SUMMARY_FILE}"
echo "==============================================================" >> "${SUMMARY_FILE}"
echo "" >> "${SUMMARY_FILE}"

echo "QuestaSim Detailed Test Log - ${TIMESTAMP}" > "${DETAILED_LOG}"
echo "==============================================================" >> "${DETAILED_LOG}"
echo "" >> "${DETAILED_LOG}"

# Function to check if test passed
check_test_result() {
    local log_file=$1
    local test_name=$2

    if [ ! -f "${log_file}" ]; then
        echo "SKIP: Log file not found"
        return 2
    fi

    # Check for success pattern
    if grep -q "\*-\* All Tests Passed \*-\*" "${log_file}" || \
       grep -q "\*-\* All Finished \*-\*" "${log_file}"; then
        return 0
    fi

    # Check for failure patterns
    if grep -q "Error:" "${log_file}" || \
       grep -q "Fatal:" "${log_file}" || \
       grep -q "\*\*\* ERROR" "${log_file}"; then
        return 1
    fi

    # If neither pattern found, consider it a failure
    return 1
}

# Function to check if a test is a negative test (expected to fail)
is_negative_test() {
    local test_path=$1
    # Tests in 'invalid' or 'error_cases' directories are expected to fail compilation
    if [[ "${test_path}" == *"/invalid/"* ]]; then
        return 0
    fi
    return 1
}

# Function to run a single test
run_test() {
    local test_path=$1
    local test_name=$(basename "${test_path}" .sv)
    local test_dir=$(dirname "${test_path}")
    local relative_path=${test_dir#${FEATURE_TESTS_DIR}/}

    # Skip archived tests and issue reproductions
    if [[ "${test_path}" == *"_archived"* ]] || [[ "${test_path}" == *"00_issue_reproductions"* ]]; then
        echo -e "${YELLOW}[SKIP]${NC} ${relative_path}/${test_name}.sv (excluded)"
        SKIPPED_TESTS=$((SKIPPED_TESTS + 1))
        SKIPPED_TEST_LIST+=("${relative_path}/${test_name}")
        return
    fi

    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    # Check if this is a negative test
    local negative_test=0
    if is_negative_test "${test_path}"; then
        negative_test=1
    fi

    # Create simulation directory
    local sim_test_dir="${SIM_DIR}/${relative_path}/${test_name}"
    mkdir -p "${sim_test_dir}"

    # Log test start
    echo "" >> "${DETAILED_LOG}"
    echo "==============================================================" >> "${DETAILED_LOG}"
    echo "Test: ${relative_path}/${test_name}" >> "${DETAILED_LOG}"
    echo "Path: ${test_path}" >> "${DETAILED_LOG}"
    echo "Negative Test: ${negative_test}" >> "${DETAILED_LOG}"
    echo "Time: $(date)" >> "${DETAILED_LOG}"
    echo "--------------------------------------------------------------" >> "${DETAILED_LOG}"

    # Run QuestaSim
    cd "${sim_test_dir}"

    # Create work library if needed
    if [ ! -d "work" ]; then
        vlib work >> "${DETAILED_LOG}" 2>&1 || true
    fi

    # Compile
    echo "Compiling..." >> "${DETAILED_LOG}"
    local compile_result=0
    if ! vlog +incdir+${COMMON_DIR} "${test_path}" >> "${DETAILED_LOG}" 2>&1; then
        compile_result=1
    fi

    # Handle negative tests (expected compilation failure)
    if [ ${negative_test} -eq 1 ]; then
        if [ ${compile_result} -eq 1 ]; then
            # Negative test failed compilation as expected
            echo -e "${CYAN}[XFAIL]${NC} ${relative_path}/${test_name}.sv (expected compilation failure)"
            echo "RESULT: EXPECTED COMPILATION FAILURE (PASS)" >> "${DETAILED_LOG}"
            PASSED_TESTS=$((PASSED_TESTS + 1))
            EXPECTED_FAIL_TESTS=$((EXPECTED_FAIL_TESTS + 1))
            EXPECTED_FAIL_LIST+=("${relative_path}/${test_name}")
        else
            # Negative test compiled successfully when it should have failed
            echo -e "${RED}[FAIL]${NC} ${relative_path}/${test_name}.sv (expected compilation failure but compiled)"
            echo "RESULT: UNEXPECTED COMPILATION SUCCESS (FAIL)" >> "${DETAILED_LOG}"
            FAILED_TESTS=$((FAILED_TESTS + 1))
            FAILED_TEST_LIST+=("${relative_path}/${test_name} (unexpected compile success)")
        fi
        return
    fi

    # Normal test - compilation failure is a real failure
    if [ ${compile_result} -eq 1 ]; then
        echo -e "${RED}[FAIL]${NC} ${relative_path}/${test_name}.sv (compilation failed)"
        echo "RESULT: COMPILATION FAILED" >> "${DETAILED_LOG}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        FAILED_TEST_LIST+=("${relative_path}/${test_name} (compilation)")
        return
    fi

    # Simulate
    echo "Simulating..." >> "${DETAILED_LOG}"
    if ! vsim -voptargs="+acc" "${test_name}" -c -do "log -r /*; run -all; quit" -l "${test_name}.log" >> "${DETAILED_LOG}" 2>&1; then
        echo -e "${RED}[FAIL]${NC} ${relative_path}/${test_name}.sv (simulation failed)"
        echo "RESULT: SIMULATION FAILED" >> "${DETAILED_LOG}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        FAILED_TEST_LIST+=("${relative_path}/${test_name} (simulation)")
        return
    fi

    # Check result
    if check_test_result "${test_name}.log" "${test_name}"; then
        echo -e "${GREEN}[PASS]${NC} ${relative_path}/${test_name}.sv"
        echo "RESULT: PASS" >> "${DETAILED_LOG}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        echo -e "${RED}[FAIL]${NC} ${relative_path}/${test_name}.sv (incorrect output)"
        echo "RESULT: FAIL (output verification)" >> "${DETAILED_LOG}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        FAILED_TEST_LIST+=("${relative_path}/${test_name} (verification)")
    fi
}

# Main execution
echo "Starting QuestaSim batch test run..."
echo "Feature tests directory: ${FEATURE_TESTS_DIR}"
echo "Simulation directory: ${SIM_DIR}"
echo ""

# Find all test files (excluding archived)
while IFS= read -r test_file; do
    run_test "${test_file}"
done < <(find "${FEATURE_TESTS_DIR}" -type f -name "*.sv" ! -path "*/_archived/*" | sort)

# Generate summary
echo "" >> "${SUMMARY_FILE}"
echo "Test Results Summary" >> "${SUMMARY_FILE}"
echo "--------------------------------------------------------------" >> "${SUMMARY_FILE}"
echo "Total Tests:   ${TOTAL_TESTS}" >> "${SUMMARY_FILE}"
echo "Passed:        ${PASSED_TESTS}" >> "${SUMMARY_FILE}"
echo "  (includes ${EXPECTED_FAIL_TESTS} expected failures)" >> "${SUMMARY_FILE}"
echo "Failed:        ${FAILED_TESTS}" >> "${SUMMARY_FILE}"
echo "Skipped:       ${SKIPPED_TESTS}" >> "${SUMMARY_FILE}"
echo "" >> "${SUMMARY_FILE}"

if [ ${FAILED_TESTS} -gt 0 ]; then
    echo "Failed Tests:" >> "${SUMMARY_FILE}"
    echo "--------------------------------------------------------------" >> "${SUMMARY_FILE}"
    for failed_test in "${FAILED_TEST_LIST[@]}"; do
        echo "  - ${failed_test}" >> "${SUMMARY_FILE}"
    done
    echo "" >> "${SUMMARY_FILE}"
fi

if [ ${EXPECTED_FAIL_TESTS} -gt 0 ]; then
    echo "Expected Failures (negative tests):" >> "${SUMMARY_FILE}"
    echo "--------------------------------------------------------------" >> "${SUMMARY_FILE}"
    for xfail_test in "${EXPECTED_FAIL_LIST[@]}"; do
        echo "  - ${xfail_test}" >> "${SUMMARY_FILE}"
    done
    echo "" >> "${SUMMARY_FILE}"
fi

if [ ${SKIPPED_TESTS} -gt 0 ]; then
    echo "Skipped Tests:" >> "${SUMMARY_FILE}"
    echo "--------------------------------------------------------------" >> "${SUMMARY_FILE}"
    for skipped_test in "${SKIPPED_TEST_LIST[@]}"; do
        echo "  - ${skipped_test}" >> "${SUMMARY_FILE}"
    done
    echo "" >> "${SUMMARY_FILE}"
fi

# Calculate pass rate
if [ ${TOTAL_TESTS} -gt 0 ]; then
    PASS_RATE=$((PASSED_TESTS * 100 / TOTAL_TESTS))
    echo "Pass Rate: ${PASS_RATE}%" >> "${SUMMARY_FILE}"
fi

echo "==============================================================" >> "${SUMMARY_FILE}"

# Display summary to console
echo ""
echo "=============================="
echo "Test Run Complete"
echo "=============================="
echo "Total:   ${TOTAL_TESTS}"
echo "Passed:  ${PASSED_TESTS} (includes ${EXPECTED_FAIL_TESTS} expected failures)"
echo "Failed:  ${FAILED_TESTS}"
echo "Skipped: ${SKIPPED_TESTS}"
if [ ${TOTAL_TESTS} -gt 0 ]; then
    echo "Pass Rate: ${PASS_RATE}%"
fi
echo ""
echo "Reports generated:"
echo "  Summary: ${SUMMARY_FILE}"
echo "  Detailed: ${DETAILED_LOG}"
echo ""

# Exit with appropriate status
if [ ${FAILED_TESTS} -gt 0 ]; then
    exit 1
else
    exit 0
fi
