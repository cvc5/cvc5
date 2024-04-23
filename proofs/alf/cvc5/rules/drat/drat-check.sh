#!/usr/bin/env bash

# This script expects an input in the form:
# (
# "<input>"
# "<proof>"
# )
# Where <input> is the name of a DIMACS file and <proof> is the name of a DRAT
# proof. We typically pipe this input to this script.

# Emptying IFS supresses word splitting by Bash
# Using '"' in IFS makes bash drop the quotes
IFS= read -r line
if [[ "$line" != "(" ]]; then
      exit 1
fi
IFS='"' read -r drop INPUT
IFS='"' read -r drop PROOF
IFS= read -r line
if [[ "$line" != ")" ]]; then
      exit 1
fi

RESULT=$(drat-trim $INPUT $PROOF)

if [[ $RESULT == *"s VERIFIED"* ]];
then
      echo "true"
      exit 0
else
      echo "error: $RESULT"
      exit 1
fi
