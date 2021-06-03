; COMMAND-LINE:  --no-check-proofs
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
(declare-fun c1 () (_ BitVec 32))
(declare-fun c2 () (_ BitVec 32))
(declare-fun out () (_ BitVec 32))
(declare-fun carry () (_ BitVec 32))
(check-sat-assuming ( (let ((_let_0 ((_ extract 1 0) b))) (let ((_let_1 ((_ extract 2 0) c1))) (let ((_let_2 (concat (_ bv0 1) (_ bv0 2)))) (let ((_let_3 ((_ extract 2 0) c2))) (let ((_let_4 (= ((_ extract 0 0) c1) (_ bv1 1)))) (let ((_let_5 (= ((_ extract 0 0) c2) (_ bv1 1)))) (let ((_let_6 ((_ extract 1 1) c1))) (let ((_let_7 (= _let_6 (_ bv1 1)))) (let ((_let_8 ((_ extract 1 1) c2))) (let ((_let_9 (= _let_8 (_ bv0 1)))) (let ((_let_10 (= _let_6 (_ bv0 1)))) (let ((_let_11 (= _let_8 (_ bv1 1)))) (let ((_let_12 (or (and _let_7 _let_9) (and _let_10 _let_11)))) (let ((_let_13 (= ((_ extract 0 0) carry) (_ bv1 1)))) (let ((_let_14 (= ((_ extract 2 2) c1) (_ bv1 1)))) (let ((_let_15 (= ((_ extract 2 2) c2) (_ bv0 1)))) (let ((_let_16 (= ((_ extract 2 2) c1) (_ bv0 1)))) (let ((_let_17 (= ((_ extract 2 2) c2) (_ bv1 1)))) (let ((_let_18 (= ((_ extract 1 1) carry) (_ bv1 1)))) (not (=> (and (= ((_ extract 1 0) a) (_ bv3 2)) (= _let_0 (_ bv3 2))) (=> (and (and (and (and (and (and (and (ite (= ((_ extract 0 0) a) (_ bv1 1)) (= _let_1 (concat (_ bv0 1) _let_0)) (= _let_1 _let_2)) (ite (= ((_ extract 1 1) a) (_ bv1 1)) (= _let_3 (concat _let_0 (_ bv0 1))) (= _let_3 _let_2))) (= ((_ extract 0 0) out) (ite (or _let_4 _let_5) (_ bv1 1) (_ bv0 1)))) (= ((_ extract 0 0) carry) (ite (and _let_4 _let_5) (_ bv1 1) (_ bv0 1)))) (= ((_ extract 1 1) out) (ite (or (and (= ((_ extract 0 0) carry) (_ bv0 1)) _let_12) (and _let_13 (and _let_10 _let_9))) (_ bv1 1) (_ bv0 1)))) (= ((_ extract 1 1) carry) (ite (or (and _let_7 _let_11) (and _let_13 _let_12)) (_ bv1 1) (_ bv0 1)))) (= ((_ extract 2 2) out) (ite (or (and (= ((_ extract 1 1) carry) (_ bv0 1)) (or (and _let_14 _let_15) (and _let_16 _let_17))) (and _let_18 (and _let_16 _let_15))) (_ bv1 1) (_ bv0 1)))) (= ((_ extract 2 2) carry) (ite (or (and _let_14 _let_17) (and _let_18 (or _let_14 _let_17))) (_ bv1 1) (_ bv0 1)))) (and (= ((_ extract 2 0) out) (_ bv1 3)) (= ((_ extract 2 0) carry) (_ bv6 3))))))))))))))))))))))))) ))
