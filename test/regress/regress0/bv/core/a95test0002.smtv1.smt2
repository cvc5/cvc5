(set-option :incremental false)
(set-info :source "Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.")
(set-info :status sat)
(set-info :difficulty "0")
(set-info :category "industrial")
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(assert (not (not (= (concat (_ bv0 16) ((_ extract 15 0) a)) a))))
(check-sat-assuming ( (not false) ))
