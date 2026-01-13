#!/bin/bash
# Run a single Verilator + UVM combination test for uvm_test_cvv
# Usage: ./run_single_set.sh <set_number>
# Example: ./run_single_set.sh 1

if [ $# -ne 1 ]; then
    echo "Usage: $0 <set_number>"
    echo ""
    echo "Available sets:"
    echo "  Set 1: Verilator-5.040 + uvm-2017"
    echo "  Set 2: Verilator-5.040 + uvm-antmicro-deprecatedApi"
    echo "  Set 3: Verilator-master + uvm-2017"
    echo "  Set 4: Verilator-master + uvm-antmicro-deprecatedApi"
    echo "  Set 5: Verilator-5.042 + uvm-2017"
    echo "  Set 6: Verilator-5.042 + uvm-antmicro-deprecatedApi"
    echo ""
    echo "Example: $0 1"
    exit 1
fi

SET_NUM=$1

# Validate set number
if [ "$SET_NUM" -lt 1 ] || [ "$SET_NUM" -gt 6 ]; then
    echo "Error: Set number must be between 1 and 6"
    exit 1
fi

# Define configurations
case $SET_NUM in
    1)
        VERILATOR_VERSION="verilator/version-5.040"
        UVM_LIB="uvm_lib/uvm-2017"
        ;;
    2)
        VERILATOR_VERSION="verilator/version-5.040"
        UVM_LIB="uvm_lib/uvm-antmicro-deprecatedApi"
        ;;
    3)
        VERILATOR_VERSION="verilator/master"
        UVM_LIB="uvm_lib/uvm-2017"
        ;;
    4)
        VERILATOR_VERSION="verilator/master"
        UVM_LIB="uvm_lib/uvm-antmicro-deprecatedApi"
        ;;
    5)
        VERILATOR_VERSION="verilator/version-5.042"
        UVM_LIB="uvm_lib/uvm-2017"
        ;;
    6)
        VERILATOR_VERSION="verilator/version-5.042"
        UVM_LIB="uvm_lib/uvm-antmicro-deprecatedApi"
        ;;
esac

VERILATOR_NAME=$(basename "$VERILATOR_VERSION")
UVM_NAME=$(basename "$UVM_LIB")

echo "========================================"
echo "Running Set ${SET_NUM} for uvm_test_cvv"
echo "Verilator: ${VERILATOR_NAME}"
echo "UVM:       ${UVM_NAME}"
echo "========================================"
echo ""

# Backup original verilator.mk
if [ ! -f "verilator.mk.original" ]; then
    cp verilator.mk verilator.mk.original
fi

# Generate new verilator.mk with selected configuration
cat > verilator.mk << 'EOF'
# DESCRIPTION: PlanV Async Fifo SV UVM Testbench
#
# Property of PlanV GmbH, 2025. All rights reserved.
# Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
# Contact: yilou.wang@planv.tech


# -------------------------------------
# Testbench setup - Auto-configured
# -------------------------------------
EOF

# Add the selected configuration
cat >> verilator.mk << EOF
VERILATOR_ROOT := \$(shell pwd)/../../../../../${VERILATOR_VERSION}
VERILATOR := \$(VERILATOR_ROOT)/bin/verilator
export VERILATOR_ROOT

UVM_ROOT ?= \$(shell pwd)/../../../../../${UVM_LIB}

# -------------------------------------
# Current Configuration: Set ${SET_NUM}
# Verilator: ${VERILATOR_NAME}
# UVM:       ${UVM_NAME}
# -------------------------------------

UVM_TEST ?= \$(UVM_TESTNAME)

DUT_FILES := \$(DV_DUT_PATH)/simple_demo_tb.sv \\
		\$(DV_DUT_PATH)/async_fifo.sv \\
		\$(DV_DUT_PATH)/empty_checker.sv \\
		\$(DV_DUT_PATH)/fifo_mem.sv \\
		\$(DV_DUT_PATH)/full_checker.sv \\
		\$(DV_DUT_PATH)/sync_2ff.sv

UVM_FILES := \$(UVM_ROOT)/src/uvm.sv

VERIF_FILES := -f \$(DV_UVMT_PATH)/uvmt_fifo.flist

VERILOG_DEFINE_FILES = \$(DUT_FILES) \\
				\$(UVM_FILES) \\
				\$(VERIF_FILES)

VERILOG_INCLUDE_DIRS = \$(UVM_ROOT)/src \\
				\$(DV_DUT_PATH) \\
				\$(DV_UVMT_PATH) \\
				\$(DV_UVME_PATH)


# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------
SIM_NAME ?= uvmt_fifo_tb
SIM_DIR := \$(SIM_NAME)-sim
COMPILE_ARGS += -DUVM_NO_DPI
COMPILE_ARGS += --prefix \$(SIM_NAME) -o \$(SIM_NAME)
COMPILE_ARGS += \$(addprefix +incdir+, \$(VERILOG_INCLUDE_DIRS))
EXTRA_ARGS += --timescale 1ns/1ps --error-limit 100
WARNING_ARGS += -Wno-lint \\
	-Wno-style \\
	-Wno-SYMRSVDWORD \\
	-Wno-IGNOREDRETURN \\
	#-Wno-CONSTRAINTIGN \\
	-Wno-ZERODLY

# -------------------------------------
# Some Useful args for debugging
# -------------------------------------
ifeq (\$(json_dump),1)
	EXTRA_ARGS += -dump-tree-json
else
endif

ifeq (\$(debug),1)
	EXTRA_ARGS += --debug --gdbbt -DVL_DEBUG=1
else
endif

# -------------------------------------
# Make UVM test with Verilator
# -------------------------------------

# Log files
VERILATE_LOG := verilate.log
COMPILE_LOG := compile.log
SIMULATE_LOG := simulate.log

.PHONY: simulate clean verilate make verilator-version

all: clean verilate make simulate

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

# +ntb_random_seed=2345

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

echo "verilator.mk updated for Set ${SET_NUM}"
echo ""
echo "Configuration:"
echo "  VERILATOR_ROOT: ../../../../../${VERILATOR_VERSION}"
echo "  UVM_ROOT:       ../../../../../${UVM_LIB}"
echo ""
echo "You can now run (from sim directory):"
echo "  make -f uvmt.mk SIMULATOR=verilator all        - Run complete build and simulation"
echo "  make -f uvmt.mk SIMULATOR=verilator verilate   - Only run Verilator elaboration"
echo "  make -f uvmt.mk SIMULATOR=verilator make       - Only compile C++"
echo "  make -f uvmt.mk SIMULATOR=verilator simulate   - Only run simulation"
echo "  make -f uvmt.mk SIMULATOR=verilator clean      - Clean build artifacts"
echo ""
echo "Or from veri-sim directory:"
echo "  cd veri-sim && make all"
echo ""
echo "Log files will be generated in veri-sim/:"
echo "  - verilate.log    : Verilator elaboration output"
echo "  - compile.log     : C++ compilation output"
echo "  - simulate.log    : Simulation output"
echo ""
echo "To restore original verilator.mk:"
echo "  cp verilator.mk.original verilator.mk"
