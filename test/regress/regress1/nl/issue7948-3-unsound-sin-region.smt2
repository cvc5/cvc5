; COMMAND-LINE: --simplification=none --tlimit=100
; EXPECT-ERROR: cvc5 interrupted by timeout.
; EXIT: -6
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (and (= a 0) (= b (cos a))))

; currently this cannot be solved due to limitations on how arguments to sin are processed
(check-sat)
