; COMMAND-LINE: --bv-abstraction
; EXPECT: sat
; Ported from Bitwuzla test/regress/solver/abstract/murxla-d9523963f3a24521.min.smt2
(set-logic QF_BV)
(set-option :global-declarations true)
(set-info :status sat)
(declare-const _x1 (_ BitVec 50))
(assert (bvugt _x1 (bvurem _x1 _x1)))
(check-sat)
