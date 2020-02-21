(set-option :incremental false)
(set-info :source "Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.")
(set-info :status unsat)
(set-info :difficulty "0")
(set-info :category "crafted")
(set-logic QF_BV)
(declare-fun bv () (_ BitVec 10))
(declare-fun a () Bool)
(check-sat-assuming ( (not (and (= ((_ extract 5 3) (_ bv96 8)) ((_ extract 4 2) (concat (_ bv121 7) ((_ extract 0 0) bv)))) (= (concat (_ bv1 1) (ite a (_ bv0 1) (_ bv1 1))) ((_ extract 1 0) (ite a (_ bv6 3) (_ bv3 3)))))) ))
