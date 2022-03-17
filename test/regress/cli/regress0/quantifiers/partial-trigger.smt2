; COMMAND-LINE: --partial-triggers
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun P (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (> y 6) (or (> x y) (P x)))))

(assert (not (P 5)))

(check-sat)
