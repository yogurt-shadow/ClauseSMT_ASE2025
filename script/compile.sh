#!/bin/bash

if [ $# -ne 2 ]; then
    echo "Usage: $0 <solver_name|all> <thread_num>"
    echo "Example: $0 clauseSMT 8"
    exit 1
fi

SOLVER_NAME=$1
THREAD_NUM=$2

SOLVERS=("clauseSMT" "nlsat" "static-look-ahead")

build_solver() {
    local solver=$1
    echo "Building solver: $solver with $THREAD_NUM threads"
    cd ../source_code/"$solver" || { echo "Directory source_code/$solver not found"; return; }
    python3 scripts/mk_make.py
    mkdir -p build
    cd build || { echo "Build directory not found"; return; }
    make -j "$THREAD_NUM"
    cd ../../..
    echo "Build finished for $solver!"
}

if [ "$SOLVER_NAME" == "all" ]; then
    for solver in "${SOLVERS[@]}"; do
        build_solver "$solver"
    done
else
    build_solver "$SOLVER_NAME"
fi
