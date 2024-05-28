; COMMAND-LINE: --proof-prune-input
; SCRUBBER: grep -E "define|unsat"
; EXPECT: unsat

(set-logic UF)
(declare-const x Bool)
(define-const p Bool x)
(assert false)
(check-sat)
