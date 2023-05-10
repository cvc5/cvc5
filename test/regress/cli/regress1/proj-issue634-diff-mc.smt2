; EXPECT: sat
; EXPECT: (
; EXPECT: )
(set-logic ALL)
(set-option :difficulty-mode model-check)
(set-option :dump-difficulty true)
(set-option :debug-check-models true)
(declare-const x Float64)
(assert (fp.isNegative x))
(check-sat)
