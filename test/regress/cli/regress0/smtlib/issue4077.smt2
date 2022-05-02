; COMMAND-LINE: --incremental
; EXPECT: sat

; Use a quantified logic to make sure that TheoryEngine creates a master
; equality engine
(set-option :global-declarations true)
(set-logic BV)
(declare-const x (_ BitVec 4))
(push)
(reset-assertions)
(assert (bvslt (bvsrem (_ bv1 4) x) (_ bv1 4)))
(check-sat)
