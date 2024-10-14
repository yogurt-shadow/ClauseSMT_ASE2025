# Data and Binary files for "ClauseSMT: Clause Level NLSAT for Nonlinear Real Arithmetic"

Author: Zhonghan Wang (wangzh@ios.ac.cn)

## Benchmark
### Download
We provide the benchmark in our Google drive 

https://drive.google.com/file/d/1sYjkQaLf6WW0P5QyUYoG8seODwzF40Ut/view?usp=sharing.

One should unzip the file to get the `QF_NRA` directory.

### Description
The benchmark in `QF_NRA` folder is collected from SMT-LIB QF_NRA track, which contains 12134 test cases.
We also provide a list file `QF_NRA/list.txt` to record relative paths of all test cases in the benchmark.

## Source Code
### Description
We recommend using Linux or WSL for running the solvers.
We provide four versions of solvers with source code (as mentioned in our paper) in `source_code/`:
| Name | Path | Description |
| --- | --- | --- |
| NLSAT | [NLSAT](source_code/nlsat/) | Internal NLSAT solver in Z3 |
| Z3 | [z3](source_code/z3/) | Z3 SMT solver |
| static-look-ahead | [static-look-ahead](source_code/static-look-ahead/) | look-ahead Mechanism with static branching heuristic |
| clauseSMT | [clauseSMT](source_code/clauseSMT/) | Final Version of our solver |

### Compilation and Running
To compiler each solver, simply go into the corresponding directory and run the following command:
```
cd <source_code/solver_name>
python3 script/mk_make.py
cd build
make -j<num_threads>
```

To run a smt2 file, simply run the solver with the smt2 file as input:
```
cd build
./z3 <*.smt2>
```

For other smt solvers, we implement the experiment using the original binary files downloads from their official websites. We also provide all binary files runnable on Linux and WSL in `binary_solvers/`.

## Experiments
### Scripts
#### Parallel Run Script
We provide a parallel script `script/parallel_run.cpp` written in C++ to run a specified solver on all test cases in the benchmark. 

The script takes three arguments:
+ **instance_list_path:** the path to the list file of test cases (default: `../QF_NRA/list.txt`)
+ **solver_path:** the path to the solver binary file (default: `../binary_solvers/z3`)
+ **output_path:** the path to collect the results (default: `../self_data/`)

```bash
cd script
g++ -O3 -o parallel_run parallel_run.cpp
./parallel_run <instance_list_path> <solver_path> <output_path>
```

#### Collecting Results
We provide a script `script/collect.py` to collect the results of all solvers on all test cases. The script takes two arguments:

+ **output_folder:** the path to the folder containing the results (default: `../self_data/`)
+ **output_file:** the path to the output csv file (default: `results.csv`)

```bash
cd script
python3 collect.py <output_folder> <output_file>
```

### Our Results in the Paper
Below shows the results of our experiments as describle in our paper, as collected in `experiment_data/`.
#### Comparison with Existing SMT Solvers
| Solver | Path | Data | Usage | Sat | Unsat | Solved |
| --- | --- | --- | --- | --- | --- | --- |
| NLSAT | [NLSAT](solvers/NLSAT) | [NLSAT_result](data/NLSAT.csv) | ./NLSAT <*.smt2> | 5541 | 5191 | 10732|
| Z3 | [z3](solvers/z3) | [z3_result](data/z3.csv) | ./z3 <*.smt2> | 5569 | 5379 | 10948|
| CVC5 | [cvc5](solvers/cvc5) | [cvc5_result](data/cvc5.csv) | ./cvc5 <*.smt2> | 5475 | 5809 | 11284|
| Yices2 | [yices2](solvers/yices2) | [yices2_result](data/yices2.csv) | ./yices2 <*.smt2> | 5372 | 5612 | 10984|
| dReal (delta=0.001) | [dReal](solvers/dReal) | [dReal_result](data/dReal.csv) | ./dReal --precision 0.001 <*.smt2> | 4811 | 4294 | 9105|
| MathSAT | [mathsat](solvers/mathsat) | [mathsat_result](data/mathsat.csv) | ./mathsat <*.smt2> | 2772 | 4583 | 7355|
| clauseSMT (Ours) | [clauseSMT](solvers/clauseSMT) | [clauseSMT_result](data/clauseSMT.csv) | ./clauseSMT <*.smt2> | 5608 | 5397 | 11005 |

#### Effect of Proposed Techniques (Ablation Study)
##### Effect of Look-Ahead Mechanism
| Solver | Description | Path | Data | Usage | Sat | Unsat | Solved |
| --- | --- | --- | --- | --- | --- | --- | --- |
| NLSAT | Decide Lowest Degree Literal | [NLSAT](solvers/NLSAT) | [NLSAT_result](data/NLSAT.csv) | ./NLSAT <*.smt2> -st | 5541 | 5191 | 10732|
| random_decide | Decide Random Literal | [random_decide](solvers/random_decide) | [random_decide_result](data/random_decide.csv) | ./random_decide <*.smt2> -st | 5505 | 5147 | 10652|
| static-look-ahead | Feasible-set based Look-Ahead | [static-look-ahead](solvers/static-look-ahead) | [static-look-ahead_result](data/static-look-ahead.csv) | ./static-look-ahead <*.smt2> -st | 5555 | 5223 | 10778|

##### Effect of Clause-Level Propagation based Branching Heuristic
| Solver | Description | Path | Data | Usage | Sat | Unsat | Solved |
| --- | --- | --- | --- | --- | --- | --- | --- |
| static-look-ahead | Static order based on degree | [static-look-ahead](solvers/static-look-ahead) | [static-look-ahead_result](data/static-look-ahead.csv) | ./static-look-ahead <*.smt2> -st | 5555 | 5223 | 10778|
| vsids-look-ahead | Dynamic order based on VSIDS | [vsids-look-ahead](solvers/vsids-look-ahead) | [vsids-look-ahead_result](data/vsids-look-ahead.csv) | ./vsids-look-ahead <*.smt2> -st | 5599 | 5321 | 10920|
| clauseSMT (Ours) | Dynamic order based on clause-level propagation | [clauseSMT](solvers/clauseSMT) | [clauseSMT_result](data/clauseSMT.csv) | ./clauseSMT <*.smt2> -st | 5608 | 5397 | 11005|
