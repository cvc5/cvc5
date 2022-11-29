; EXPECT: (error "Term of kind `eqrange` not supported in default mode, try `--arrays-exp`.")
; EXIT: 1
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(assert (eqrange a a 0 0))
(check-sat)
