; COMMAND-LINE: -i --sat-solver=cadical
; DISABLE-TESTER: proof
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic NIA)
(declare-fun T () Int)
(declare-fun F () Int)
(assert (distinct T F))
(declare-fun g () Int)
(push)
(assert false)
(check-sat)
(check-sat)
(check-sat)
(check-sat)
(pop)
(assert (= g T))
(assert (= g F))
(push)
(assert false)
(check-sat)
