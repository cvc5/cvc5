; COMMAND-LINE:
; COMMAND-LINE: --check-proofs-complete
; EXPECT: unsat
; EXPECT: true
; EXPECT: true
; Explicit completeness checking must work in safe/stable builds alongside a
; regular option, whether enabled through the command line or set-option.
(set-option :check-proofs-complete true)
(set-option :simplification none)
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(get-option :check-proofs)
(get-option :produce-proofs)
