#!/bin/bash

cd build

git checkout main
make clean; ccache -C; make -j15 &> ~/main.log

git checkout gmp_large
make clean; ccache -C; make -j15 &> ~/gmp_large.log

cat ~/gmp_large.log |grep conversion|sort > ~/gmp_large_conversion.log
cat ~/main.log |grep conversion | sort > ~/main_conversion.log

vimdiff ~/gmp_large_conversion.log ~/main_conversion.log

