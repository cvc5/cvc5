#!/usr/bin/env bash

set -e -o pipefail

dir="$DESTDIR$1"

find "$dir/include/cvc5/" -type f \
  -exec sed -i'' -e 's/include.*"api\/cpp\/\(.*\)"/include <cvc5\/\1>/' {} +

find "$dir/include/cvc5/" -type f \
  -exec sed -i'' -e 's/"cvc5_export.h"/<cvc5\/cvc5_export.h>/' {} +
