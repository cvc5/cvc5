; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x Bool)
(declare-const x9 Bool)
(declare-const x95 Bool)
(declare-fun n () (Array (_ BitVec 64) (_ BitVec 72)))
(assert (and (forall ((u (_ BitVec 64))) (and x9 (not (or x x9)) (= (_ bv0 1) ((_ extract 71 71) (select (ite x95 n (store n (_ bv0 64) (concat (_ bv1 1) (_ bv0 3) (_ bv0 64) (_ bv0 3) (ite (and x95 (not (or x x9))) (_ bv0 1) (_ bv1 1))))) (_ bv0 64))))))))
(check-sat)
