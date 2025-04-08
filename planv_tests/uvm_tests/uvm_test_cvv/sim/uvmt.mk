# DESCRIPTION: PlanV Async Fifo SV UVM Testbench
#
# Property of PlanV GmbH, 2025. All rights reserved.
# Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
# Contact: yilou.wang@planv.tech

SIMULATOR ?= $(DV_SIMULATOR)
# SIM_RESULTS ?= 
RTL_PATH := $(shell pwd)/../../../../uvm_tests
TEST_PATH := uvm_test_cvv

# UVM Environment
export DV_UVMT_PATH = $(RTL_PATH)/$(TEST_PATH)/uvmt
export DV_UVME_PATH = $(RTL_PATH)/$(TEST_PATH)/uvme
export DV_UVMA_PATH = $(RTL_PATH)/$(TEST_PATH)/uvma

export DV_UVMA_WR_RD_PATH = $(DV_UVMA_PATH)/uvma_wr_rd

export DV_DUT_PATH = $(RTL_PATH)/DUT

UVM_TESTNAME ?= uvmt_fifo_base_test_c

RTLSRC_VLOG_TB_TOP := $(RTL_PATH)/DUT/simple_demo_tb.sv


ifeq ($(SIMULATOR), vsim)
include $(RTL_PATH)/$(TEST_PATH)/sim/vsim.mk
else 
ifeq ($(SIMULATOR), verilator)
include $(RTL_PATH)/$(TEST_PATH)/sim/verilator.mk
else
endif
endif
 