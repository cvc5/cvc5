(set-logic ALL)
(set-info :status unsat)

(declare-fun x () Real)

(assert (< (* x x) 0.0))

(check-sat)
