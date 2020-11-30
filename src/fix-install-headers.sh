#!/usr/bin/env bash

set -e -o pipefail

dir="$DESTDIR$1"

find "$dir/include/cvc4/" -type f \
  -exec sed -i'' -e 's/include.*"\(.*\)"/include <cvc4\/\1>/' {} +
