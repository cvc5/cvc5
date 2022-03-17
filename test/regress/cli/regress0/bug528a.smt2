; EXPECT: unsat
; COMMAND-LINE: --incremental --repeat-simp
; DISABLE-TESTER: unsat-core
(set-logic QF_LIA)
(declare-fun i () Int)
(assert (ite (= i 0) false true))
(push 1)
(assert (= i 0))
(check-sat)
