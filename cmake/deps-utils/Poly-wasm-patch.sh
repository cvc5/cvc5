#!/bin/sh

# Comment the enabled_count variable inside the factorization.c file because 
#   emscripten detects that this variable is useless and aborts the compilation.
sed -i 's/.*enabled_count/\/\/&/g' $1/src/Poly-EP/src/upolynomial/factorization.c