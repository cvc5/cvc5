; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --unsat-cores-mode=sat-proof
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: (a)
(set-option :produce-unsat-assumptions true)
(set-logic QF_LIA)
(declare-fun t () Int)
(declare-fun p () Bool)
(declare-fun o () Bool)
(declare-fun a () Bool)
(assert (=> a (< 0 (ite o 0 (ite p 0 t)))))
(check-sat)
(assert p)
(check-sat-assuming (true))
(check-sat-assuming (a))
(get-unsat-assumptions)
