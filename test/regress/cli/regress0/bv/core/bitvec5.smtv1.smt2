(set-option :incremental false)
(set-info :source "Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.")
(set-info :status unsat)
(set-info :difficulty "0")
(set-info :category "crafted")
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
(declare-fun d () (_ BitVec 32))
(declare-fun e () (_ BitVec 32))
(check-sat-assuming ( (not (and (=> (and (and (= ((_ extract 31 0) a) ((_ extract 31 0) b)) (= ((_ extract 31 16) a) ((_ extract 15 0) c))) (= ((_ extract 31 8) b) ((_ extract 23 0) d))) (= ((_ extract 11 8) c) ((_ extract 19 16) d))) (=> (= ((_ extract 30 0) e) ((_ extract 31 1) e)) (= ((_ extract 0 0) e) ((_ extract 31 31) e))))) ))
