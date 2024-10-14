import sys
import json
import argparse
import os
import subprocess
import random

def value2str(v):
    if v >= 0:
        return str(v)
    else:
        res = str(-v)
        return '(- ' + res + ')'

def generate_literal(r1, r2):
    """
    (<= (+ (* x x) (* (- 1) coeff2 x) coeff3) 0)
    """
    coeff2 = r1 + r2
    coeff3 = r1 * r2
    return '(<= (+ (* x x) (* (- 1) ' + value2str(coeff2) + ' x) ' + value2str(coeff3) + ') 0)'

def generate_clause(r_list):
    """
    (or (<= (+ (* x x) (* (- 1) coeff2 x) coeff3) 0)
         (<= (+ (* x x) (* (- 1) coeff2 x) coeff3) 0)
    """
    res = '(assert (or  '
    for r1, r2 in r_list:
        res += generate_literal(r1, r2) + ' '
    res += '))\n'
    return res

def generate_smt2():
    res = '(set-logic QF_NRA)\n\n'
    res += '(declare-const x Real)\n\n'
    r_list = []
    # ; [-1000, -1], [-999, 0], ..., [-2, 997], ..., [2000, 3000]
    # ; [-1001, -3], [-1000, -2], ..., [-3, 995], ..., [2001, 3001]
    # ; [-1002, -5], [-1001, -4], ..., [-4, 993], ..., [2002, 3002]
    # ; [2500, 2600]

    start_left, start_right = -1000, -1
    for i in range(3):
        r_list = []
        left, right = start_left, start_right
        while True:
            print(left, right)
            r_list.append((left, right))
            if left == -2 - i:
                r_list.append((2000 + i - 1, 3000 + i - 1))
                res += generate_clause(r_list)
                break
            left += 1
            right += 1
        start_left -= 1
        start_right -= 2
    r_list = []
    r_list.append((2500, 2600))
    res += generate_clause(r_list)
    res += "(check-sat)\n(exit)\n"
    return res


if __name__ == "__main__":
    smt2 = generate_smt2()
    output = "craft1.smt2"
    if os.path.exists(output):
        os.remove(output)
    with open(output, 'w') as f:
        f.write(smt2)
