; COMMAND-LINE: --uf-ho
; EXPECT: sat
(set-logic QF_AUFBVLIA)
(set-option :uf-ho true)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c (Int) Int)
(declare-fun d (Int Int) Int)
(assert (xor (= c (d a)) (= c (d b))))
(check-sat)
