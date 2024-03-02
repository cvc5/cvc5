; COMMAND-LINE: --fmf-bound --mbqi
; EXPECT: unsat
;; introduces fresh Skolem in a trusted step
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-sort a 0)
(declare-datatypes ((prod 0)) (((Pair (gx a) (gy a)))))
(declare-fun p () prod)
(assert (forall ((x a) (y a)) (not (= p (Pair x y)))))
; problem is unsat, currently unknown with fmf-bound
(check-sat)
