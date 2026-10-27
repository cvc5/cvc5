; EXPECT: sat
(set-logic ALL)
(declare-const x (Seq Bool))
(declare-const x1 (Seq Bool))
(assert (seq.suffixof (seq.replace_all x1 x (seq.unit (seq.suffixof x1 (seq.++ x1 x1)))) x))
(assert (distinct x (seq.++ x1 x)))
(check-sat)
