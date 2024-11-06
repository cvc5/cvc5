(set-logic ALL)
(set-info :status sat)

(declare-const x Int)
(assert (seq.contains (seq.at (seq.unit (bag false x)) x) (seq.unit (bag false x))))
(check-sat)
