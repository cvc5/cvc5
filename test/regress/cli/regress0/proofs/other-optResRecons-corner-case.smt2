; COMMAND-LINE: --no-early-exit --check-proofs --proof-granularity=theory-rewrite --proof-check=lazy -q --dag-thresh=0
; EXIT: 0
; SCRUBBER: grep -v -E '.*'
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert (not (ite (ite (ite p false (ite (ite p false true) false true)) false true) (ite (ite (ite (ite p q false) false true) true (ite (ite p (ite q false true) true) false true)) (ite (ite (ite r q false) (ite p q r) true) (ite (ite (ite p r false) (ite false true (ite p r false)) true) (ite (ite p (ite q r false) false) (ite p r false) (ite (ite q (ite p r false) false) false true)) false) false) false) false)))
(check-sat)
