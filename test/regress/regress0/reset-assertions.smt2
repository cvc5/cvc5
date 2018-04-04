; EXPECT: sat
; EXPECT: sat
(set-logic QF_ALL)
(set-option :incremental true)
(set-option :produce-models true)

(declare-fun x () Real)
(declare-fun y () Real)
(assert (> x 0.0))
(assert (> y 0.0))
(assert (= (+ (* 2 x) y) 4))
(check-sat)
(reset-assertions)

(declare-fun a () (Array Int Int))
(assert (= (select a 4) 10))
(check-sat)
