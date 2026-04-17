; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic ALL)
(declare-fun b () Real)
(declare-fun r () (Array Real Real))
(assert (= 0.0 (select r (* b b))))
(assert (= 1.0 (select r 1.0)))
(check-sat)
