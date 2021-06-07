; COMMAND-LINE: --hol
; EXPECT: sat
(set-logic QF_AUFBVLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c (Int) Int)
(declare-fun d (Int Int) Int)
(assert (xor (= c (d a)) (= c (d b))))
(check-sat)
