# -------------------------------------
# Testbench setup
# -------------------------------------
VERILATOR := verilator
ifdef VERILATOR_ROOT
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
endif

CMD = $(pwd)
SV_PATHS := /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests/t_recursive
# SV_FILES := $(foreach path,$(SV_PATHS),$(wildcard $(path)/*sv))

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------

VERILOG_DEFINE_FILES = /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests/t_recursive/tb_top.sv
SIM_NAME = tb_top

SIM_DIR := $(SIM_NAME)-sim
COMPILE_ARGS += -DUVM_NO_DPI -CFLAGS "-std=gnu++20"
COMPILE_ARGS += --prefix $(SIM_NAME) -o $(SIM_NAME)
EXTRA_ARGS += --timescale 1ns/1ps --error-limit 100
WARNING_ARGS += -Wno-lint \
	-Wno-style \
	-Wno-SYMRSVDWORD \
	-Wno-IGNOREDRETURN \
	-Wno-ZERODLY \
	-Wno-SIDEEFFECT \
	-Wno-CONSTRAINTIGN

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

all: clean verilate simulate

verilate:
$(SIM_DIR)/$(SIM_NAME).mk:
	$(VERILATOR) --cc --exe --main --trace --trace-structs --timing -Mdir $(SIM_DIR) \
	${COMPILE_ARGS} ${EXTRA_ARGS} \
	+incdir+${SV_PATHS} ${SV_PATHS}/my_pkg.sv ${SV_PATHS}/my_if.sv ${VERILOG_DEFINE_FILES} \
	${WARNING_ARGS}

$(SIM_DIR)/$(SIM_NAME): $(SIM_DIR)/$(SIM_NAME).mk
	$(MAKE) -j${NPROC} -C $(SIM_DIR) $(BUILD_ARGS) -f $(SIM_NAME).mk

simulate: $(SIM_DIR)/$(SIM_NAME).mk $(SIM_DIR)/$(SIM_NAME)
	$(SIM_DIR)/$(SIM_NAME)

clean:
	rm -rf $(SIM_DIR)
	rm -rf *.vcd

verilator-version:
	@echo "Running $(VERILATOR) --version"
	@$(VERILATOR) --version

vsim:
	@if [ ! -d "work" ]; then vlib work; fi
	vlog /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests/t_recursive/tb_top.sv || { echo "vlog failed"; exit 1; }
	vsim -voptargs="+acc" tb_top -c -do "log -r /*; run -all; quit" -l tb_top.log || { echo "vsim failed"; exit 1; }

vsim-gui:
	@if [ ! -d "work" ]; then vlib work; fi
	vlog /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/feature_tests/t_recursive/tb_top.sv || { echo "vlog failed"; exit 1; }
	vsim -voptargs="+acc" tb_top || { echo "vsim failed"; exit 1; }

