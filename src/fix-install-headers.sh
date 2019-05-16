#!/bin/bash

dir=$1
find "$dir/include/cvc4/" -type f | \
  xargs sed -i 's/include.*"\(.*\)"/include <cvc4\/\1>/'
