import os

def main():
    commands = [
        # "cd /home/yilou/Desktop/OSVISE/Randomization_Enable_4_Verilator-planV-/verilator_planv && ./configure && make",
        "make json_dump=1 debug=1"
    ]

    for command in commands:
        print(f"**************************\nRunning command: {command}\n**************************")
        os.system(command)

if __name__ == '__main__':
    main() 