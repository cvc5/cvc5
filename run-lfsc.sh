#!/bin/bash

./proofs/lfsc_checker/lfsc-checker --run-scc  ./proofs/signatures/sat.plf ./proofs/signatures/smt.plf ./proofs/signatures/th_base.plf ./proofs/signatures/th_bv.plf ./proofs/signatures/th_bv_bitblast.plf $1
