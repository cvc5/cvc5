; EXPECT: sat
(set-logic ALL)
(declare-const x Bool)
(assert (and (exists ((v Int)) (or (< (abs v) 0) x))))
(check-sat)
