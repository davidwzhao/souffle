#!/bin/bash

# Enable debugging and logging of shell operations
# that are executed.
set -e
set -x

ulimit -c unlimited -S
# Run from the test directory if we don't need the unit tests
if [[ "$SOUFFLE_CATEGORY" != *"Unit"* ]]
then
  cd tests
fi
TESTSUITEFLAGS="-j2 $TESTRANGE" make check -j2
