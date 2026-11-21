; REQUIRES: unrestricted-mode
; COMMAND-LINE: --minimal-unsat-cores --quiet
; COMMAND-LINE: --minimal-unsat-cores --quiet --check-unsat-cores
; COMMAND-LINE: --minimal-unsat-cores --quiet --tlimit-per=1000
; EXPECT: unsat
; EXPECT: (
; EXPECT: easy
; EXPECT: hard
; EXPECT: )
; The original query is easy, but removing the first assertion leaves a hard
; nonlinear problem. Core minimization must time out and retain the assertion.
(set-logic QF_NIA)
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(assert (! (= x 0) :named easy))
(assert (! (= (* x x x) 564838384999) :named hard))
(check-sat)
(get-unsat-core)
