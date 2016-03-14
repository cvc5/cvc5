#!/bin/bash

./builds/x86_64-unknown-linux-gnu/debug-staticbinary-proof/proofs/lfsc_checker/lfsc-checker \
    ./proofs/signatures/sat.plf \
    ./proofs/signatures/smt.plf \
    ./proofs/signatures/th_base.plf \
    ./proofs/signatures/th_bv.plf \
    ./proofs/signatures/th_bv_bitblast.plf \
    ./proofs/signatures/th_arrays.plf \
    ./proofs/signatures/th_real.plf \
    ./proofs/signatures/th_int.plf \
    $1


# ./proofs/lfsc_checker/lfsc-checker
