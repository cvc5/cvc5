#!/usr/bin/env bash

# This script expects an input in the form:
# (
# "<input>"
# )
# Where <input> is the name of a DIMACS file.
# We typically pipe this input to this script.

# Emptying IFS supresses word splitting by Bash
# Using '"' in IFS makes bash drop the quotes
IFS= read -r line
if [[ "$line" != "(" ]]; then
      exit 1
fi
IFS='"' read -r drop INPUT
IFS= read -r line
if [[ "$line" != ")" ]]; then
      exit 1
fi

# First, call cadical to construct the DRAT proof.
# We disable binary, since otherwise drat-trim fails to check sometimes.
cadical $INPUT $INPUT.proof --binary=false > /dev/null

# Then, check with drat-trim and record the result in RESULT
RESULT=$(cat $INPUT.proof | drat-trim $INPUT)
rm -f $INPUT.proof

# If the result contains the text "VERIFIED", we are successful.
if [[ $RESULT == *"s VERIFIED"* ]];
then
      echo "true"
      exit 0
else
      echo "error: $RESULT"
      exit 1
fi

