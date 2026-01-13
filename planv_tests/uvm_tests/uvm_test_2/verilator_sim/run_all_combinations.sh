#!/bin/bash
# Automated test runner for all Verilator + UVM combinations
# This script tests 6 combinations: 3 Verilator versions × 2 UVM libraries

set -e  # Exit on error (disabled for this script to continue on failures)

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Get the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Results directory
RESULTS_DIR="test_results"
rm -rf "$RESULTS_DIR"
mkdir -p "$RESULTS_DIR"

# Test configurations
VERILATOR_VERSIONS=(
    "verilator/master"
    "verilator/version-5.042"
    "verilator/version-5.040"
)

UVM_LIBS=(
    "uvm_lib/uvm-2017"
    "uvm_lib/uvm-antmicro-deprecatedApi"
)

# Function to update Makefile with specific configuration
update_makefile() {
    local verilator_path=$1
    local uvm_path=$2

    # Backup original Makefile
    cp Makefile Makefile.bak

    # Create new Makefile with selected configuration
    cat > Makefile << EOF
# -------------------------------------
# Testbench setup
# -------------------------------------
# Auto-generated configuration for testing
VERILATOR_ROOT := \$(shell pwd)/../../../../${verilator_path}
VERILATOR := \$(VERILATOR_ROOT)/bin/verilator
export VERILATOR_ROOT

UVM_ROOT := \$(shell pwd)/../../../../${uvm_path}

UVM_TEST ?= case1_test

VERILOG_DEFINE_FILES = \${UVM_ROOT}/src/uvm.sv ../af_pkg.sv ../af_bfm.sv ../top.sv ../../DUT/async_fifo.sv ../../DUT/empty_checker.sv ../../DUT/fifo_mem.sv ../../DUT/full_checker.sv ../../DUT/sync_2ff.sv
VERILOG_INCLUDE_DIRS = \${UVM_ROOT}/src ../../DUT ../. ../uvm_class

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------
SIM_NAME ?= top
SIM_DIR := \$(SIM_NAME)-sim
COMPILE_ARGS += -DUVM_NO_DPI
COMPILE_ARGS += --prefix \$(SIM_NAME) -o \$(SIM_NAME)
COMPILE_ARGS += \$(addprefix +incdir+, \$(VERILOG_INCLUDE_DIRS))
EXTRA_ARGS += --timescale 1ns/1ps --error-limit 100
WARNING_ARGS += -Wno-lint \\
	-Wno-style \\
	-Wno-SYMRSVDWORD \\
	-Wno-IGNOREDRETURN \\
	-Wno-CONSTRAINTIGN \\
	-Wno-ZERODLY
ifeq (\$(json_dump),1)
	EXTRA_ARGS += -dump-tree-json
else
endif

# -------------------------------------
# Make UVM test with Verilator
# -------------------------------------

.PHONY: simulate clean verilate verilator-version

all: clean verilate make simulate

# Log files
VERILATE_LOG := verilate.log
COMPILE_LOG := compile.log
SIMULATE_LOG := simulate.log

verilate:
	@echo "=== Starting Verilator elaboration at \$\$(date) ===" > \$(VERILATE_LOG)
	\$(VERILATOR) --cc --exe --main --trace --trace-structs --timing -Mdir \$(SIM_DIR) \\
	\${COMPILE_ARGS} \${EXTRA_ARGS} \\
	\${VERILOG_DEFINE_FILES} \\
	\${WARNING_ARGS} 2>&1 | tee -a \$(VERILATE_LOG)
	@echo "=== Verilator elaboration completed at \$\$(date) ===" >> \$(VERILATE_LOG)

make: verilate
	@echo "=== Starting C++ compilation at \$\$(date) ===" > \$(COMPILE_LOG)
	\$(MAKE) -j\${NPROC} -C \$(SIM_DIR) \$(BUILD_ARGS) -f \$(SIM_NAME).mk 2>&1 | tee -a \$(COMPILE_LOG)
	@echo "=== C++ compilation completed at \$\$(date) ===" >> \$(COMPILE_LOG)

simulate: make
	@echo "=== Starting simulation at \$\$(date) ===" > \$(SIMULATE_LOG)
	@echo "Test: \$(UVM_TEST)" >> \$(SIMULATE_LOG)
	@echo "========================================" >> \$(SIMULATE_LOG)
	\$(SIM_DIR)/\$(SIM_NAME) +UVM_TESTNAME=\$(UVM_TEST) 2>&1 | tee -a \$(SIMULATE_LOG)
	@echo "========================================" >> \$(SIMULATE_LOG)
	@echo "=== Simulation completed at \$\$(date) ===" >> \$(SIMULATE_LOG)

clean:
	rm -rf simv*.daidir csrc
	rm -rf csrc* simv*
	rm -rf \$(SIM_DIR)
	rm -rf dump.vcd
	rm -f \$(VERILATE_LOG) \$(COMPILE_LOG) \$(SIMULATE_LOG)

verilator-version:
	@echo "Running \$(VERILATOR) --version"
	@\$(VERILATOR) --version
EOF
}

# Function to run a single test configuration
run_test() {
    local set_num=$1
    local verilator_path=$2
    local uvm_path=$3
    local verilator_name=$(basename "$verilator_path")
    local uvm_name=$(basename "$uvm_path")

    echo -e "${YELLOW}========================================${NC}"
    echo -e "${YELLOW}Set${set_num}: ${verilator_name} + ${uvm_name}${NC}"
    echo -e "${YELLOW}========================================${NC}"

    # Create result directory for this configuration
    local result_dir="${RESULTS_DIR}/Set${set_num}_${verilator_name}_${uvm_name}"
    mkdir -p "$result_dir"

    # Update Makefile
    update_makefile "$verilator_path" "$uvm_path"

    # Run the test and capture status
    local status="UNKNOWN"
    local error_stage=""

    # Try to run make all (timeout: 10 minutes)
    if timeout 600 make all > "${result_dir}/full_output.log" 2>&1; then
        status="${GREEN}PASS${NC}"
    else
        # Check which stage failed
        if [ ! -f "verilate.log" ]; then
            status="${RED}VERILATE_ERROR${NC}"
            error_stage="Verilate"
        elif [ ! -f "compile.log" ]; then
            status="${RED}COMPILE_ERROR${NC}"
            error_stage="Compile"
        elif [ ! -f "simulate.log" ]; then
            status="${RED}SIMULATE_ERROR${NC}"
            error_stage="Simulate"
        else
            status="${RED}UNKNOWN_ERROR${NC}"
            error_stage="Unknown"
        fi
    fi

    # Copy log files to result directory
    [ -f "verilate.log" ] && cp verilate.log "${result_dir}/"
    [ -f "compile.log" ] && cp compile.log "${result_dir}/"
    [ -f "simulate.log" ] && cp simulate.log "${result_dir}/"

    # Save configuration
    cat > "${result_dir}/config.txt" << EOF
Set Number: ${set_num}
Verilator: ${verilator_name}
UVM Library: ${uvm_name}
Status: ${status}
Error Stage: ${error_stage}
Test Date: $(date)
EOF

    echo -e "Result: ${status}"
    if [ -n "$error_stage" ]; then
        echo -e "Failed at: ${error_stage}"
    fi
    echo ""

    # Clean up for next test
    make clean > /dev/null 2>&1 || true

    # Return status for summary
    echo "$set_num|$verilator_name|$uvm_name|$status|$error_stage"
}

# Main test execution
echo -e "${GREEN}Starting automated test suite${NC}"
echo -e "${GREEN}Testing 6 combinations of Verilator + UVM${NC}"
echo ""

# Array to store results
declare -a results

# Test counter
set_num=1

# Run all combinations
for verilator in "${VERILATOR_VERSIONS[@]}"; do
    for uvm in "${UVM_LIBS[@]}"; do
        result=$(run_test "$set_num" "$verilator" "$uvm")
        results+=("$result")
        set_num=$((set_num + 1))
    done
done

# Restore original Makefile
if [ -f "Makefile.bak" ]; then
    mv Makefile.bak Makefile
fi

# Generate summary report
echo -e "${GREEN}========================================${NC}"
echo -e "${GREEN}TEST SUMMARY${NC}"
echo -e "${GREEN}========================================${NC}"
echo ""

summary_file="${RESULTS_DIR}/SUMMARY.txt"
cat > "$summary_file" << EOF
Verilator + UVM Combination Test Results
=========================================
Test Date: $(date)

Configuration Matrix:
--------------------
EOF

for result in "${results[@]}"; do
    IFS='|' read -r set ver uvm stat err <<< "$result"
    echo "Set${set}: ${ver} + ${uvm}" | tee -a "$summary_file"
    echo "  Status: ${stat}" | tee -a "$summary_file"
    if [ -n "$err" ] && [ "$err" != "Unknown" ]; then
        echo "  Failed at: ${err}" | tee -a "$summary_file"
    fi
    echo "" | tee -a "$summary_file"
done

cat >> "$summary_file" << EOF

Expected Results (from Makefile comments):
-------------------------------------------
Set1: Verilator-5.040 + uvm-2017                    -> Compile Error
Set2: Verilator-5.040 + uvm-antmicro-deprecatedApi  -> Pass
Set3: Verilator-master + uvm-2017                   -> Compile Error
Set4: Verilator-master + uvm-antmicro-deprecatedApi -> Pass
Set5: Verilator-5.042 + uvm-2017                    -> Compile/Simulate Error
Set6: Verilator-5.042 + uvm-antmicro-deprecatedApi  -> Pass

Results Location:
-----------------
All logs saved in: ${RESULTS_DIR}/
Each set has its own directory with:
  - verilate.log (Verilator elaboration)
  - compile.log (C++ compilation)
  - simulate.log (Simulation execution)
  - config.txt (Configuration details)
  - full_output.log (Complete output)
EOF

echo -e "${GREEN}========================================${NC}"
echo -e "${GREEN}All tests completed!${NC}"
echo -e "${GREEN}Results saved in: ${RESULTS_DIR}/${NC}"
echo -e "${GREEN}Summary report: ${summary_file}${NC}"
echo -e "${GREEN}========================================${NC}"
