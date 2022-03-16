; This was causing trouble in CVC4 r1434 due to mishandling of ITE
; removal for PARAMETERIZED kinds.
; Thanks to Andrew Reynolds for catching this.
(set-logic QF_UF)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun c () Bool)
(declare-fun g (U) Bool)
(assert (g (ite c a a)))
(check-sat)
(exit)
