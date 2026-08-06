#!/bin/bash

cat preamble-compiled.egg > output.egg
./transform.py input.egg >> output.egg
cargo r --bin egglog output.egg
