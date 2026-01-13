# -------------------------------------
# Testbench setup
# -------------------------------------
VERILATOR := verilator
ifdef VERILATOR_ROOT
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
endif

CMD = $(pwd)
SV_PATHS := .
SV_FILES := $(foreach path,$(SV_PATHS),$(wildcard $(path)/*sv))

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------

VERILOG_DEFINE_FILES = /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests/constrained_random/t_fuxian_inherit.sv
SIM_NAME = t_fuxian_inherit

SIM_DIR := $(SIM_NAME)-sim
COMPILE_ARGS += -DUVM_NO_DPI -CFLAGS "-std=gnu++20"
COMPILE_ARGS += --prefix $(SIM_NAME) -o $(SIM_NAME)
EXTRA_ARGS += --timescale 1ns/1ps --error-limit 100
WARNING_ARGS +=

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


.PHONY: simulate clean verilate verilator-version make-vsim make-vsim-gui

all: clean verilate make simulate

verilate:
	$(VERILATOR) --cc --exe --main --trace --trace-structs --timing -Mdir $(SIM_DIR) \
	${COMPILE_ARGS} ${EXTRA_ARGS} \
	${VERILOG_DEFINE_FILES} \
	${WARNING_ARGS}

make:
	$(MAKE) -j${NPROC} -C $(SIM_DIR) $(BUILD_ARGS) -f $(SIM_NAME).mk

simulate:
	$(SIM_DIR)/$(SIM_NAME)

clean:
	rm -rf $(SIM_DIR)
	rm -rf *.vcd

verilator-version:
	@echo "Running $(VERILATOR) --version"
	@$(VERILATOR) --version

vsim:
	@if [ ! -d "work" ]; then vlib work; fi
	vlog /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests/constrained_random/t_fuxian_inherit.sv || { echo "vlog failed"; exit 1; }
	vsim -voptargs="+acc" t_fuxian_inherit -c -do "log -r /*; run -all; quit" -l t_fuxian_inherit.log || { echo "vsim failed"; exit 1; }

vsim-gui:
	@if [ ! -d "work" ]; then vlib work; fi
	vlog /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests/constrained_random/t_fuxian_inherit.sv || { echo "vlog failed"; exit 1; }
	vsim -voptargs="+acc" t_fuxian_inherit || { echo "vsim failed"; exit 1; }

