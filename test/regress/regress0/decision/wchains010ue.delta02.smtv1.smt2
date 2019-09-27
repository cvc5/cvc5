; COMMAND-LINE: --decision=justification
; EXPECT: unsat
(set-option :incremental false)
(set-info :status unsat)
(set-logic QF_AUFBV)
(declare-fun v6 () (_ BitVec 32))
(declare-fun v7 () (_ BitVec 32))
(declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
(check-sat-assuming ( (let ((_let_0 ((_ extract 23 16) v6))) (let ((_let_1 ((_ extract 23 16) v7))) (not (= (_ bv0 1) (bvand (ite (= (_ bv0 2) ((_ extract 1 0) v6)) (_ bv1 1) (_ bv0 1)) (bvnot (ite (= (store (store (store (store (store a1 v6 _let_0) (_ bv0 32) (_ bv0 8)) v7 _let_1) (_ bv1 32) (_ bv0 8)) (_ bv0 32) (_ bv0 8)) (store (store (store (store a1 (_ bv0 32) (_ bv0 8)) v7 _let_1) (_ bv1 32) (_ bv0 8)) v6 _let_0)) (_ bv1 1) (_ bv0 1)))))))) ))
