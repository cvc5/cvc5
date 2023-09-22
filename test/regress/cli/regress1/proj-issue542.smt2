; EXPECT: unsat
; EXPECT: (
; EXPECT: )
(set-logic ALL)
(set-option :difficulty-mode model-check)
(set-option :dump-difficulty true)
(assert (seq.nth (seq.unit (>= 0.0 (arccos 0.0))) 0))
(check-sat)
