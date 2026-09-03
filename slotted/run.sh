#!/bin/bash

pat="$1"

for x in $(find tests -type f | sort)
do
    if [[ ! "$x" == *"$pat"* ]]; then
        continue
    fi
    echo "Test: $x"
    cat preamble-compiled.egg > output.egg
    ./transform.py "$x" >> output.egg
    cargo r --bin egglog output.egg
done
