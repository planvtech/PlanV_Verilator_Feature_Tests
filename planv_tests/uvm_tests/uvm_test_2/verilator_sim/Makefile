# -------------------------------------
# Testbench setup - Set 4
# -------------------------------------
VERILATOR_ROOT := $(shell pwd)/../../../../verilator/master
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
export VERILATOR_ROOT

UVM_ROOT := $(shell pwd)/../../../../uvm_lib/uvm-antmicro-deprecatedApi

UVM_TEST ?= case1_test

VERILOG_DEFINE_FILES = ${UVM_ROOT}/src/uvm.sv ../af_pkg.sv ../af_bfm.sv ../top.sv ../../DUT/async_fifo.sv ../../DUT/empty_checker.sv ../../DUT/fifo_mem.sv ../../DUT/full_checker.sv ../../DUT/sync_2ff.sv
VERILOG_INCLUDE_DIRS = ${UVM_ROOT}/src ../../DUT ../. ../uvm_class

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------
SIM_NAME ?= top
SIM_DIR := $(SIM_NAME)-sim
COMPILE_ARGS += -DUVM_NO_DPI
COMPILE_ARGS += --prefix $(SIM_NAME) -o $(SIM_NAME)
COMPILE_ARGS += $(addprefix +incdir+, $(VERILOG_INCLUDE_DIRS))
EXTRA_ARGS += --timescale 1ns/1ps --error-limit 100
WARNING_ARGS += -Wno-lint \
	-Wno-style \
	-Wno-SYMRSVDWORD \
	-Wno-IGNOREDRETURN \
	-Wno-CONSTRAINTIGN \
	-Wno-ZERODLY
ifeq ($(json_dump),1)
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
	@echo "=== Starting Verilator elaboration at $$(date) ===" > $(VERILATE_LOG)
	$(VERILATOR) --cc --exe --main --trace --trace-structs --timing -Mdir $(SIM_DIR) \
	${COMPILE_ARGS} ${EXTRA_ARGS} \
	${VERILOG_DEFINE_FILES} \
	${WARNING_ARGS} 2>&1 | tee -a $(VERILATE_LOG)
	@echo "=== Verilator elaboration completed at $$(date) ===" >> $(VERILATE_LOG)

make: verilate
	@echo "=== Starting C++ compilation at $$(date) ===" > $(COMPILE_LOG)
	$(MAKE) -j${NPROC} -C $(SIM_DIR) $(BUILD_ARGS) -f $(SIM_NAME).mk 2>&1 | tee -a $(COMPILE_LOG)
	@echo "=== C++ compilation completed at $$(date) ===" >> $(COMPILE_LOG)

simulate: make
	@echo "=== Starting simulation at $$(date) ===" > $(SIMULATE_LOG)
	@echo "Test: $(UVM_TEST)" >> $(SIMULATE_LOG)
	@echo "========================================" >> $(SIMULATE_LOG)
	$(SIM_DIR)/$(SIM_NAME) +UVM_TESTNAME=$(UVM_TEST) 2>&1 | tee -a $(SIMULATE_LOG)
	@echo "========================================" >> $(SIMULATE_LOG)
	@echo "=== Simulation completed at $$(date) ===" >> $(SIMULATE_LOG)

clean:
	rm -rf simv*.daidir csrc
	rm -rf csrc* simv*
	rm -rf $(SIM_DIR)
	rm -rf dump.vcd
	rm -f $(VERILATE_LOG) $(COMPILE_LOG) $(SIMULATE_LOG)

verilator-version:
	@echo "Running $(VERILATOR) --version"
	@$(VERILATOR) --version
