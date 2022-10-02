; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-const x Bool)
(declare-fun a () Real)
(declare-fun r () Real)
(declare-fun v () Real)
(assert (and (xor (= a 1.0) x) (= 1.0 (- v (exp (* r v))))))
(check-sat)
