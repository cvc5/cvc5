; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun v () String)
(declare-fun X () Int)
(declare-fun t () Int)
(assert (and (< t (- 15)) (< (- 38) t)))
(assert (not (str.< (str.++ (str.++ (str.from_int X) (str.from_int (- t))) v) "3lA")))
(check-sat)
