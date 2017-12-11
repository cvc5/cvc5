(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((A 0) (B 0)) (
((a (sa B)))
((e1) (e2 (se2 A)))
))

(declare-const x1 A)
(declare-const x2 B)

(assert (distinct x1 (a x2)))

(declare-const x3 A)

(assert (distinct x2 (e2 x3)))

(check-sat)

