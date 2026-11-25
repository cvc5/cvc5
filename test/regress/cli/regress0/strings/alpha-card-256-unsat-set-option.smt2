; EXPECT: unsat
(set-option :strings-alpha-card 256)
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 1))
; unsat since all characters have code point at most 255
(assert (>= (str.to_code x) 256))
(check-sat)
