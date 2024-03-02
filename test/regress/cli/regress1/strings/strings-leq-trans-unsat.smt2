; COMMAND-LINE: --strings-exp
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; timeout with unsat cores
;; introduces fresh Skolem in a trusted step
; DISABLE-TESTER: alethe
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(assert (str.<= x y))
(assert (str.<= y w))
(declare-fun xp () String)
(assert (= x (str.++ "G" xp)))
(assert (= w "E"))
(check-sat)
