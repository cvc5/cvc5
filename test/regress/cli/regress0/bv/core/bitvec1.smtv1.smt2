; COMMAND-LINE:
; EXPECT: unsat
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
(declare-fun res () (_ BitVec 32))
(check-sat-assuming ( (let ((_let_0 (= ((_ extract 0 0) a) (_ bv1 1)))) (let ((_let_1 (= ((_ extract 0 0) b) (_ bv1 1)))) (let ((_let_2 (= ((_ extract 0 0) c) (_ bv1 1)))) (let ((_let_3 ((_ extract 0 0) res))) (let ((_let_4 (= ((_ extract 1 1) b) (_ bv1 1)))) (let ((_let_5 (ite (= ((_ extract 1 1) a) (_ bv1 1)) (not _let_4) _let_4))) (let ((_let_6 ((_ extract 1 1) c))) (let ((_let_7 ((_ extract 1 1) res))) (not (=> (and (and (and (= ((_ extract 1 0) a) (_ bv1 2)) (= ((_ extract 1 0) b) (_ bv1 2))) (and (ite (and _let_0 _let_1) _let_2 (= ((_ extract 0 0) c) (_ bv0 1))) (ite (ite _let_0 (not _let_1) _let_1) (= _let_3 (_ bv1 1)) (= _let_3 (_ bv0 1))))) (and (ite (or (and (= ((_ extract 1 1) a) (_ bv1 1)) _let_4) (and _let_5 _let_2)) (= _let_6 (_ bv1 1)) (= _let_6 (_ bv0 1))) (ite (ite _let_2 (not _let_5) _let_5) (= _let_7 (_ bv1 1)) (= _let_7 (_ bv0 1))))) (and (= ((_ extract 1 0) res) (_ bv2 2)) (= ((_ extract 1 0) c) (_ bv1 2))))))))))))) ))
