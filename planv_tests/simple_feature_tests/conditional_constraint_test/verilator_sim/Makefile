# -------------------------------------
# Testbench setup
# -------------------------------------
VERILATOR := verilator
ifdef VERILATOR_ROOT
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
endif

CMD = $(pwd)
UVM_ROOT ?=/home/yilou/Desktop/OSVISE/uvm/uvm-verilator

VERILOG_INCLUDE_DIRS = ${UVM_ROOT}/src

SV_PATHS := .
SV_FILES := $(foreach path,$(SV_PATHS),$(wildcard $(path)/*svh) $(wildcard $(path)/*svh))

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------
ifeq ($(test),1)
	VERILOG_DEFINE_FILES = ../implication_con_and_if_else_con.sv
	SIM_NAME = implication_con_and_if_else_con
else
	VERILOG_DEFINE_FILES = ../test_4_conditional_constrain.sv
	SIM_NAME = test_4_conditional_constrain
endif

SIM_DIR := $(SIM_NAME)-sim
COMPILE_ARGS += -DUVM_NO_DPI
COMPILE_ARGS += --prefix $(SIM_NAME) -o $(SIM_NAME)
COMPILE_ARGS += $(addprefix +incdir+, $(VERILOG_INCLUDE_DIRS))
EXTRA_ARGS += --timescale 1ns/1ps --error-limit 100
WARNING_ARGS += -Wno-lint \
	-Wno-style \
	-Wno-SYMRSVDWORD \
	-Wno-IGNOREDRETURN \
	-Wno-ZERODLY \
	-Wno-CONSTRAINTIGN

ifeq ($(json_dump),1)
	EXTRA_ARGS += -dump-tree-json
else
endif

ifeq ($(debug),1)
	EXTRA_ARGS += --debug --gdbbt -CFLAGS -DVL_DEBUG=1
else
endif

.PHONY: simulate clean verilate verilator-version

all: clean verilate simulate

verilate:
# -------------------------------------
# Make UVM test with Verilator
# -------------------------------------
$(SIM_DIR)/$(SIM_NAME).mk: $(SV_FILES)
	$(VERILATOR) --cc --exe --main --trace --trace-structs --timing -Mdir $(SIM_DIR) \
	${COMPILE_ARGS} ${EXTRA_ARGS} \
	${VERILOG_DEFINE_FILES} \
	${WARNING_ARGS}

$(SIM_DIR)/$(SIM_NAME): $(SIM_DIR)/$(SIM_NAME).mk
	$(MAKE) -j${NPROC} -C $(SIM_DIR) $(BUILD_ARGS) -f $(SIM_NAME).mk

simulate: $(SIM_DIR)/$(SIM_NAME).mk $(SIM_DIR)/$(SIM_NAME)
	$(SIM_DIR)/$(SIM_NAME)

clean:
	rm -rf simv*.daidir csrc
	rm -rf csrc* simv*
	rm -rf $(SIM_DIR)
	rm -rf dump.vcd

verilator-version:
	@echo "Running $(VERILATOR) --version"
	@$(VERILATOR) --version