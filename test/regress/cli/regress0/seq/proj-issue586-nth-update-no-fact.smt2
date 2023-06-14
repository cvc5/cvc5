; EXPECT: sat
(set-logic ALL)
(set-option :seq-array eager)
(declare-const x String)
(declare-const x5 (Bag String))
(assert (str.<= x (seq.nth (seq.update (seq.unit x) (bag.card x5) (seq.unit x)) (bag.card x5))))
(check-sat)
