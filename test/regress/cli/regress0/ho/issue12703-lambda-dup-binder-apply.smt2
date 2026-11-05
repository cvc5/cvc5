; Renaming a duplicate binder is not an instance of alpha-equivalence, so the
; proof of this benchmark has a trust step, which safe builds do not permit.
; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic HO_ALL)
(declare-fun h (Int Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= h (lambda ((x Int) (x Int)) x)))
(assert (not (= (h a b) (@ (@ h a) b))))
(check-sat)
