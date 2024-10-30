# PlanV Verilator Feature Tests

Welcome to the PlanV Verilator Feature Tests repository! 
This repo is designed to help you run and contribute tests for Verilator-based projects. Below, you'll find instructions on how to get started, run tests, and contribute.

## Repository Structure

├── .github

│ └── workflows

│ │ └── PlanV_verilator_feature_tests.yml

├── scripts

│ ├── run.sh

│ └── ciSystemRuner.sh

│ └── ..

├── planv_tests

│ ├── feature_tests

│ │ └── ...

│ └── uvm_tests

│ └── ...

## Getting Started

### Prerequisites

Ensure you have the following installed:
- GCC (preferably gcc-12)
- Python 3 with `z3-solver`
- Other dependencies as listed in the `.github/workflows/PlanV_verilator_feature_tests.yml` file

### Setup, Build and Run Tests

For details, refer to the `.github/workflows/PlanV_verilator_feature_tests.yml` file.

## Detailed Workflow
For details on the workflow, check the .github/workflows/PlanV_verilator_feature_tests.yml file. This file defines the CI/CD pipeline, including dependencies installation, setup, build, and test execution.

The scripts/ciSystemRunner.sh script contains the logic for setting up the environment, building the project, and running the tests.

### Local Testing Setup

Testing for the features/regress test, you can run on the local setup. 
The scripts/run script contains the logic for setting up the log and sim folder, building the project, and running the tests.

#### Usage
Run the script with the following format:
./scripts/run -b <branch_name> -t <test_dir/test_file> 

branch_name: Specifies the development branch from the [PlanV Verilator repository.](https://github.com/planvtech/verilator.git)
test_dir/test_file: Path to the .sv file within the planv_tests directory, or the directory containing .sv files in planv_tests

Example usage:

chmod +x scripts/run
./scripts/run -b master -t planv_tests/feature_tests/assertions
./scripts/run -b master -t planv_tests/feature_tests/assertions/t_assertion_immediate.sv 

#### Generated Artifacts
The scripts/run command generates essential artifacts to aid in debugging and analysis:
* Log files and HTML reports for enhanced visualization are saved in the logs directory.
* Simulation artifacts and Makefiles for the tests are located in the sim directory.


├──logs                                                                  ├──sim          

|  ├──feature_tests 													 |  ├──feature_tests

|  | └── Path_to_test_dir												 |  | └── Path_to_test_dir

|  | |   └── <test>.log													 |  | |   └── Makefile

|  | └── test_report.log												 |  | |   └── <test_name>-sim

|  | └── fancy_test_report_<branch>.html								 |  | |   |    └── ...

|  ├── uvm_tests
  
|  |	└── <test>.log

|  ├── run.log

## Contributing
We welcome contributions! If you've created a test that you'd like to share:

1. Fork the repository
2. Create a new branch for your test
3. Add your test to the appropriate directory (feature_tests/ or uvm_tests/)
4. Commit your changes
5. Push to the branch
6. Create a Pull Request on GitHub

### Guidelines
1. Ensure your test is well-documented.
2. Follow the existing code style and structure.
3. Update the README.md if your contribution includes significant changes.

## Support
If you have any questions or need help, feel free to open an issue on GitHub or contact the maintainers.
