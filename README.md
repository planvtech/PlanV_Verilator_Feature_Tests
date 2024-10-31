# PlanV Verilator Feature Tests

Copyright (c) 2024 [PlanV](https://planv.tech/)

Welcome to the PlanV Verilator Feature Tests repository! 
This repo is designed to help you run and contribute tests for Verilator-based projects. Below, you'll find instructions on how to get started, run tests, and contribute.

## Repository Structure

├── .github

│ └── workflows

│ │ └── PlanV_verilator_feature_tests.yml

├── scripts

│ └── setup_and_build

├── planv_tests

│ ├── feature_tests

│ │ └── ...

│ └── uvm_tests

│ └── ...

## Getting Started

### Prerequisites

Ensure you have the following installed:
- Verilator
- GCC (preferably gcc-12)
- Python 3 with `z3-solver`
- Other dependencies as listed in the `.github/workflows/PlanV_verilator_feature_tests.yml` file

### Setup, Build and Run Tests

For details, refer to the `.github/workflows/PlanV_verilator_feature_tests.yml` file.

## Detailed Workflow
For details on the workflow, check the .github/workflows/PlanV_verilator_feature_tests.yml file. This file defines the CI/CD pipeline, including dependencies installation, setup, build, and test execution.

The scripts/setup_and_build script contains the logic for setting up the environment, building the project, and running the tests.

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
