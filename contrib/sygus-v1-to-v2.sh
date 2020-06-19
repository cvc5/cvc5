#!/bin/bash
# This is a simple script for converting v1 sygus files to v2.

# Show how to use the script
if [[ "$#" < 3 || ! -f "$1" || ! -f "$2" ]]; then
  echo "Usage: $0 [<path to cvc4>] [<path to sygus file>] [<path to output file>] [<additional cvc4 options>*]"
  exit 1
fi

output=$("$1" "$2" --lang=sygus1 --dump-to="$3" --output-lang=sygus2 --dump=raw-benchmark --preprocess-only "${@:4}" 2>&1)

exitCode=$?

if [[ "$exitCode" == 0 ]]; then
  # Remove incremental and produce-models options
  sed -i '/(set-option :incremental false)/d' "$3"
  sed -i '/(set-option :produce-models "true")/d' "$3"
else
  echo "$1 failed with exit code $exitCode:"
  echo "$output"
fi
