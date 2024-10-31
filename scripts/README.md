The current script includes the following files:

* set_build_run_functions: This file contains the functions for setup, build, and run, which can be called by other scripts.
* setup_framework: Unlike the previous setup framework located in the test folder, this script generates a new simulation folder to store the Makefile and simulation-generated files. The advantage of this approach is that after running the simulation once, it makes it easier to clean up the previous simulation files for subsequent runs.
* run: This script is intended for users running simulations locally and accepts two arguments to specify the branch and test directory.
* ciSystemRunner: This script is designed for GitHub Actions and will run all tests in sequence.
* polish_to_html.py: A Python script that converts the log files generated from simulations into more readable HTML files.