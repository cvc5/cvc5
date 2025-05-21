; EXPECT: unsat
(set-logic ALL)
(declare-const x1 (Seq (Seq (Seq Bool))))
(assert (seq.suffixof x1 (seq.unit (seq.unit (seq.unit false)))))
(assert (= (str.len x1) 1))
(assert (seq.suffixof x1 (seq.unit (seq.unit (seq.unit true)))))
(check-sat)
