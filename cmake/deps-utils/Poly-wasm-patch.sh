#!/bin/sh

sed -i 's/.*enabled_count/\/\/&/g' $1/src/Poly-EP/src/upolynomial/factorization.c