#!/bin/bash


# Enable debugging and logging of shell operations
# that are executed.
set -e
set -x

make -j2 install

#generate a simple program
A=".decl A()
A().
.printsize A"

echo "$A" > a.dl

# test if an installed souffle compiles and runs
souffle -c a.dl
