; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(define-fun b ((bv (_ BitVec 4))) (_ BitVec 4) bv)
(define-fun i ((index (_ BitVec 4)) (bv (_ BitVec 4))) (_ BitVec 4) (b bv))
(assert (= (_ bv0 8) (bvxor (_ bv1 8) ((_ zero_extend 4) (i (_ bv0 4) (_ bv0 4))))))
(check-sat)
