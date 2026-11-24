; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (or (not (= (bvite #b1 x y) x)) (not (= (bvite #b0 x y) y))))
(check-sat)
