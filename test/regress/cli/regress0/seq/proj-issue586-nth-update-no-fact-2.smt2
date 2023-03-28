; EXPECT: sat
(set-logic ALL)
(set-option :seq-array eager)
(declare-const x String)
(declare-fun f (String) Int)
(declare-const x5 String)
(assert (str.<= x (seq.nth (seq.update (seq.unit x) (f x5) (seq.unit x)) (f x5))))
(check-sat)
