#!/bin/bash
# Run a single Verilator + UVM combination test
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
echo "Running Set ${SET_NUM}"
echo "Verilator: ${VERILATOR_NAME}"
echo "UVM:       ${UVM_NAME}"
echo "========================================"
echo ""

# Backup original Makefile
if [ ! -f "Makefile.original" ]; then
    cp Makefile Makefile.original
fi

# Update Makefile for this configuration
cat > Makefile << EOF
# -------------------------------------
# Testbench setup - Set ${SET_NUM}
# -------------------------------------
VERILATOR_ROOT := \$(shell pwd)/../../../../${VERILATOR_VERSION}
VERILATOR := \$(VERILATOR_ROOT)/bin/verilator
export VERILATOR_ROOT

UVM_ROOT := \$(shell pwd)/../../../../${UVM_LIB}

UVM_TEST ?= case0_test

VERILOG_DEFINE_FILES = \${UVM_ROOT}/src/uvm.sv ../sv_fifo_pkg.sv ../sv_fifo_interface.sv ../sv_tb_top.sv ../../DUT/simple_demo_tb.sv ../../DUT/async_fifo.sv ../../DUT/empty_checker.sv ../../DUT/fifo_mem.sv ../../DUT/full_checker.sv ../../DUT/sync_2ff.sv
VERILOG_INCLUDE_DIRS = ../../DUT ../. ../sv_uvm_class \${UVM_ROOT}/src

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------
SIM_NAME ?= simple_demo_tb
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

echo "Makefile updated for Set ${SET_NUM}"
echo "Configuration:"
echo "  VERILATOR_ROOT: ../../../../${VERILATOR_VERSION}"
echo "  UVM_ROOT:       ../../../../${UVM_LIB}"
echo ""
echo "You can now run:"
echo "  make all          - Run complete build and simulation"
echo "  make verilate     - Only run Verilator elaboration"
echo "  make make         - Only compile C++"
echo "  make simulate     - Only run simulation"
echo "  make clean        - Clean build artifacts"
echo ""
echo "Log files will be generated:"
echo "  - verilate.log    : Verilator elaboration output"
echo "  - compile.log     : C++ compilation output"
echo "  - simulate.log    : Simulation output"
echo ""
echo "To restore original Makefile:"
echo "  cp Makefile.original Makefile"
