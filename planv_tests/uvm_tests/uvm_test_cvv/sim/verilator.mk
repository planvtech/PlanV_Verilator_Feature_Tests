# DESCRIPTION: PlanV Async Fifo SV UVM Testbench
#
# Property of PlanV GmbH, 2025. All rights reserved.
# Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
# Contact: yilou.wang@planv.tech


# -------------------------------------
# Testbench setup
# -------------------------------------
# Select Verilator version (uncomment one)
VERILATOR_ROOT := $(shell pwd)/../../../../../verilator/master
# VERILATOR_ROOT := /home/yilou/Desktop/OSVISE/planvtech/yilou_repo/yilou_verilator/verilator
# VERILATOR_ROOT := $(shell pwd)/../../../../../verilator/version-5.042
# VERILATOR_ROOT := $(shell pwd)/../../../../../verilator/version-5.040

VERILATOR := $(VERILATOR_ROOT)/bin/verilator
export VERILATOR_ROOT

# Select UVM library (uncomment one)
# UVM_ROOT ?= $(shell pwd)/../../../../../uvm_lib/uvm-2017
UVM_ROOT ?= $(shell pwd)/../../../../../uvm_lib/uvm-antmicro-deprecatedApi

# -------------------------------------
# Configuration Matrix (for reference)
# Set1: Verilator-5.040 + uvm-2017
# Set2: Verilator-5.040 + uvm-antmicro-deprecatedApi
# Set3: Verilator-master + uvm-2017
# Set4: Verilator-master + uvm-antmicro-deprecatedApi
# Set5: Verilator-5.042 + uvm-2017
# Set6: Verilator-5.042 + uvm-antmicro-deprecatedApi
# -------------------------------------

UVM_TEST ?= $(UVM_TESTNAME)

DUT_FILES := $(DV_DUT_PATH)/simple_demo_tb.sv \
		$(DV_DUT_PATH)/async_fifo.sv \
		$(DV_DUT_PATH)/empty_checker.sv \
		$(DV_DUT_PATH)/fifo_mem.sv \
		$(DV_DUT_PATH)/full_checker.sv \
		$(DV_DUT_PATH)/sync_2ff.sv

UVM_FILES := $(UVM_ROOT)/src/uvm.sv

VERIF_FILES := -f $(DV_UVMT_PATH)/uvmt_fifo.flist

VERILOG_DEFINE_FILES = $(DUT_FILES) \
				$(UVM_FILES) \
				$(VERIF_FILES)

VERILOG_INCLUDE_DIRS = $(UVM_ROOT)/src \
				$(DV_DUT_PATH) \
				$(DV_UVMT_PATH) \
				$(DV_UVME_PATH)


# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------
SIM_NAME ?= uvmt_fifo_tb
SIM_DIR := $(SIM_NAME)-sim
COMPILE_ARGS += -DUVM_NO_DPI
COMPILE_ARGS += --prefix $(SIM_NAME) -o $(SIM_NAME)
COMPILE_ARGS += $(addprefix +incdir+, $(VERILOG_INCLUDE_DIRS))
EXTRA_ARGS += --timescale 1ns/1ps --error-limit 100
WARNING_ARGS += -Wno-lint \
	-Wno-style \
	-Wno-SYMRSVDWORD \
	-Wno-IGNOREDRETURN \
	#-Wno-CONSTRAINTIGN \
	-Wno-ZERODLY

# -------------------------------------
# Some Useful args for debugging
# -------------------------------------
ifeq ($(json_dump),1)
	EXTRA_ARGS += -dump-tree-json
else
endif

ifeq ($(debug),1)
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

# +ntb_random_seed=2345

clean:
	rm -rf simv*.daidir csrc
	rm -rf csrc* simv*
	rm -rf $(SIM_DIR)
	rm -rf dump.vcd
	rm -f $(VERILATE_LOG) $(COMPILE_LOG) $(SIMULATE_LOG)

verilator-version:
	@echo "Running $(VERILATOR) --version"
	@$(VERILATOR) --version
