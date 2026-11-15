; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic QF_NIRA)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (/_total x y) (/_total (to_real x) (to_real y)))))
(check-sat)
