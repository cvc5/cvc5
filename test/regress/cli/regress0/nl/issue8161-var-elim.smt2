; EXPECT: sat
(set-logic QF_NRA)
(declare-fun r5 () Real)
(declare-fun r7 () Real)
(declare-fun r26 () Real)
(assert (or (= 3 r5) (= r7 0)))
(assert (and (< r26 0.0) (< r7 r26)))
(assert (or (> r5 1) (= 0.0 (/ (- r26 (/ r5 0.0)) r7))))
(check-sat)
