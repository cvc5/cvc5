; COMMAND-LINE: --produce-difficulty
; EXPECT: sat
(set-logic ALL)
(declare-const x Bool)
(declare-fun a () Real)
(declare-fun r () Real)
(assert (xor (= 0.0 (/ 0.0 a)) (and x (= 0.0 (/ r a r)))))
(check-sat)
