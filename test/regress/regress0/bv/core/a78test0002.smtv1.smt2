(set-option :incremental false)
(set-info :source "Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.")
(set-info :status sat)
(set-info :difficulty "0")
(set-info :category "industrial")
(set-logic QF_BV)
(declare-fun r1 () (_ BitVec 16))
(assert (not (= r1 (_ bv0 16))))
(assert (not (not (= (concat (_ bv0 16) r1) (_ bv65535 32)))))
(check-sat-assuming ( (not false) ))
