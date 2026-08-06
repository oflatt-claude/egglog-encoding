#!/bin/bash

for x in $(find tests -type f | sort)
do
    echo "Test: $x"
    cat preamble-compiled.egg > output.egg
    ./transform.py "$x" >> output.egg
    cargo r --bin egglog output.egg
done
