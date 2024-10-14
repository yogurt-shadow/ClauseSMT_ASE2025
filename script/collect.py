import os, sys

class DataPoint:
    # Benchmark, Result, Time, Memory
    def __init__(self, name):
        self.name = name
        self.result, self.time, self.memory = None, None, None

def process_point(name, lines):
    dp = DataPoint(name)
    if "unsat" in lines[0]:
        dp.result = "unsat"
    elif "sat" in lines[0]:
        dp.result = "sat"
    else:
        dp.result = "unknown"
    for i in range(1, len(lines)):
        lines[i].replace(')', '')
        lines[i].strip()
        if ":time" in lines[i]:
            dp.time = float(lines[i].split(' ')[-1])
        elif ":memory" in lines[i]:
            dp.memory = float(lines[i].split(' ')[-1])
    return dp 

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python collect.py <folder> <output>")
        sys.exit(1)
    dps = {}
    total, sat, unsat, solved, unsolved = 0, 0, 0, 0, 0
    folder = sys.argv[1]
    files = os.listdir(folder)
    for file in files:
        file_name = file.replace('.txt', '')
        lines = open(folder + '/' + file).readlines()
        dps[file_name] = process_point(file_name, lines)
    output_file = open(sys.argv[2], 'w')
    output_file.write("Benchmark Result Time Memory\n")
    for name in dps:
        dp = dps[name]
        output_file.write(f"{dp.name} {dp.result} {dp.time} {dp.memory}\n")
        if dp.result == "sat":
            sat += 1
        elif dp.result == "unsat":
            unsat += 1
        if dp.result != "unknown":
            solved += 1
        else:
            unsolved += 1
        total += 1
    output_file.close()
    print("Done!")
    print(f"Total: {total}")
    print(f"Solved: {solved}")
    print(f"Unsolved: {unsolved}")
    print(f"Sat: {sat}")
    print(f"Unsat: {unsat}")
