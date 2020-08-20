; COMMAND-LINE: --unconstrained-simp
; EXPECT: (error "Cannot use unconstrained simplification in this logic, due to (possibly internally introduced) quantified formula.")
; EXIT: 1
(set-logic ALL)
(set-info :status unsat)
(declare-fun a () Int)
(assert (= (div a 2) 2))
(assert (= (div a 3) 0))
(check-sat)
