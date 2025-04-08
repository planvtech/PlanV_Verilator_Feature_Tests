# DESCRIPTION: PlanV Async Fifo SV UVM Testbench
#
# Property of PlanV GmbH, 2025. All rights reserved.
# Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
# Contact: yilou.wang@planv.tech


# -------------------------------------
# Testbench setup
# -------------------------------------
VERILATOR := verilator
ifdef VERILATOR_ROOT
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
endif

UVM_ROOT ?= $(shell pwd)/../../../../../uvm-verilator

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

.PHONY: simulate clean verilate verilator-version

all: clean verilate simulate

verilate:
$(SIM_DIR)/$(SIM_NAME).mk:
	$(VERILATOR) --cc --exe --main --trace --trace-structs --timing -Mdir $(SIM_DIR) \
	${COMPILE_ARGS} ${EXTRA_ARGS} \
	${VERILOG_DEFINE_FILES} \
	${WARNING_ARGS}

$(SIM_DIR)/$(SIM_NAME): $(SIM_DIR)/$(SIM_NAME).mk
	$(MAKE) -j${NPROC} -C $(SIM_DIR) $(BUILD_ARGS) -f $(SIM_NAME).mk

simulate: $(SIM_DIR)/$(SIM_NAME).mk $(SIM_DIR)/$(SIM_NAME)
	$(SIM_DIR)/$(SIM_NAME) +UVM_TESTNAME=$(UVM_TEST) +ntb_random_seed=2345

clean:
	rm -rf simv*.daidir csrc
	rm -rf csrc* simv*
	rm -rf $(SIM_DIR)
	rm -rf dump.vcd

verilator-version:
	@echo "Running $(VERILATOR) --version"
	@$(VERILATOR) --version