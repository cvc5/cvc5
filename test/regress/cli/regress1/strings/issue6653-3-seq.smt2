; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(set-option :strings-lazy-pp false)
(declare-fun z () Int)
(declare-fun a () (Seq Int))
(assert (not (= (seq.nth a 1) (seq.nth a z))))
(assert (= z (- 1)))
(check-sat)
