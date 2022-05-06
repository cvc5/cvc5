; EXPECT: unsat
(set-logic HO_UFLIA)
(set-info :status unsat)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)

(assert (or (= P Q) (= P R)))

(assert (not (Q 0)))
(assert (not (R 3)))

(assert (forall ((x Int)) (P x)))

(check-sat)
