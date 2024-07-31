import os
import sys

def run_test0():
    commands = [
        "cd ../../verilator && ./configure && make",
        "make json_dump=1 debug=1"
    ]

    for command in commands:
        print(f"**************************\nRunning command: {command}\n**************************")
        os.system(command)

def run_test1():
    commands = [
        "cd ../../verilator && ./configure && make",
        #"make test=1 json_dump=1 debug=1"
    ]

    for command in commands:
        print(f"**************************\nRunning command: {command}\n**************************")
        os.system(command)

def main():
    if len(sys.argv) != 2:
        print("Usage: python run_command.py <test_number>")
        return
    
    test_number = sys.argv[1]

    if test_number == '-1':
        run_test1()
    elif test_number == '-0':
        run_test0()
    else:
        print("Invalid test number.")
        
if __name__ == '__main__':
    main() 