import os
import sys
import csv

# 20161105-Sturm-MBO/mbo_E10E24.smt2
def process_name(file):
    split_parts = file.split('/')
    family_name, file_name_pre = split_parts[0], split_parts[-1]
    file_name = file_name_pre.rsplit('.', 1)[0]
    return file_name, family_name


'''
benchmark   family    result
'''
def collect_infos(folder, files, data):
    data.append(["benchmark", "family", "result", "time", "memory", "conflict", "decision", "stage"])
    timeout, total, sat, unsat, unknown = 0, 0, 0, 0, 0
    for file in files:
        total += 1
        file_name, family_name = process_name(file)
        num_line = 0
        _memory, _time, _conflict, _decision, _stage = 0, 0, 0, 0, 0
        for line in open(folder + file_name + ".txt", 'r', encoding='utf-8'):
            line = line.strip()
            if num_line == 0:
                res = line
                if res == "timeout":
                    timeout += 1
                elif res == "sat":
                    sat += 1
                elif res == "unsat":
                    unsat += 1
                else:
                    unknown += 1
            else:
                elements = line.split()
                if len(elements) > 1 and elements[0] == ":memory":
                    curr = elements[1]
                    if curr[-1] == ')':
                        curr = curr[0:-1]
                    _memory = float(curr)
                elif len(elements) > 1 and elements[0] == ":time":
                    curr = elements[1]
                    if curr[-1] == ')':
                        curr = curr[0:-1]
                    _time = float(curr)
                elif len(elements) > 1 and elements[0] == ":nlsat-conflicts":
                    curr = elements[1]
                    if curr[-1] == ')':
                        curr = curr[0:-1]
                    _conflict = float(curr)
                elif len(elements) > 1 and elements[0] == ":nlsat-decisions":
                    curr = elements[1]
                    if curr[-1] == ')':
                        curr = curr[0:-1]
                    _decision = float(curr)
                elif len(elements) > 1 and elements[0] == ":nlsat-stages":
                    curr = elements[1]
                    if curr[-1] == ')':
                        curr = curr[0:-1]
                    _stage = float(curr)
            num_line += 1
        data.append([file_name, family_name, res, _time, _memory, _conflict, _decision, _stage])
    data.append([])
    data.append(["total", "sat", "unsat", "solved", "timeout", "unsolved"])
    data.append([total, sat, unsat, sat + unsat, timeout, unknown])
    print("sat: ", sat)
    print("unsat: ", unsat)
    print("solved: ", sat + unsat)
    print("total: ", total)
    
if __name__ == "__main__":
    folder = sys.argv[1]
    result = sys.argv[2]
    if os.path.exists(result):
        os.remove(result)
    file_names = [line.strip() for line in open("list.txt", "r").readlines()]
    data = []
    collect_infos(folder, file_names, data)
    with open(result, "w") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerows(data)
    
