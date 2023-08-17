; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-const x (Set Bool))
(declare-const x1 (Seq (Set Bool)))
(declare-const x4 (Set (Seq (Set Bool))))
(assert (distinct (set.choose x4) (set.choose (set.singleton x1)) (seq.unit (set.minus x (set.singleton false)))))
(check-sat)
