# DESCRIPTION: PlanV Async Fifo SV UVM Testbench
#
# Property of PlanV GmbH, 2025. All rights reserved.
# Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
# Contact: yilou.wang@planv.tech

TOPLEVEL_MODULE = uvmt_fifo_tb
TESTBENCH_MODULE = uvmt_fifo_tb
SIMULATOR = vsim

UVM_ROOT ?=/opt/questasim/verilog_src/uvm-1.2
UVM_TEST ?= $(UVM_TESTNAME)

USES_DPI = 1
DPI_INCLUDE ?= /opt/questasim/include

VSIM_COV ?= -coverage

ifeq ($(USES_DPI),1)
	DPILIB_VLOG_OPT = 
	DPILIB_VSIM_OPT = -sv_lib /opt/questasim/uvm-1.2/linux_x86_64/uvm_dpi
	DPILIB_TARGET = dpi_lib$(BITS)
else
	DPILIB_VLOG_OPT = +define+UVM_NO_DPI
	DPILIB_VSIM_OPT =
	DPILIB_TARGET =
endif

LIBDIR = $(UVM_ROOT)/src/lib
LIBNAME = uvm_dpi

DUT_FILES = $(DV_DUT_PATH)/simple_demo_tb.sv \
		$(DV_DUT_PATH)/async_fifo.sv \
		$(DV_DUT_PATH)/empty_checker.sv \
		$(DV_DUT_PATH)/fifo_mem.sv \
		$(DV_DUT_PATH)/full_checker.sv \
		$(DV_DUT_PATH)/sync_2ff.sv

UVM_FILES = $(UVM_ROOT)/src/uvm.sv

VERIF_FILES = -f $(DV_UVMT_PATH)/uvmt_fifo.flist

VERILOG_DEFINE_FILES = $(DUT_FILES) \
				$(UVM_FILES) \
				$(VERIF_FILES)

VERILOG_INCLUDE_DIRS = $(UVM_ROOT)/src \
				$(DV_DUT_PATH) \
				$(DV_UVMT_PATH) \
				$(DV_UVME_PATH)

WORK_DIR = work

VSIM_OPTS = -t ps -voptargs=+acc -uvmcontrol=all +UVM_VERBOSITY=UVM_MEDIUM $(DPILIB_VSIM_OPT) -do "run -all" -l simulate.log

ifeq ($(GUI),1)
	VSIM_OPTS += -gui
else
	VSIM_OPTS += -c
endif

VLOG_INCDIR := $(foreach dir,$(VERILOG_INCLUDE_DIRS),+incdir+$(dir))

.PHONY: all compile simulate clean

all: clean compile simulate

compile:
	vlib $(WORK_DIR)
	vmap work $(WORK_DIR)
	vlog -work $(WORK_DIR) $(VLOG_INCDIR) $(VERILOG_DEFINE_FILES)

simulate: compile
	$(SIMULATOR) -64 -lib $(WORK_DIR) $(TESTBENCH_MODULE) $(VSIM_OPTS) +UVM_TESTNAME=$(UVM_TEST)

clean:
	rm -rf $(WORK_DIR)
	rm -f dump.vcd modelsim.ini simulate.log tr_db.log transcript vsim.wlf vsim_stacktrace.vstf
