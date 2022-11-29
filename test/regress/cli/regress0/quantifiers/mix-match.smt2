; COMMAND-LINE: --enum-inst
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun P (Real) Bool)
(assert (forall ((x Int)) (P (to_real x))))

(declare-fun a () Real)
(assert (is_int a))
(assert (not (P a)))

(check-sat)
