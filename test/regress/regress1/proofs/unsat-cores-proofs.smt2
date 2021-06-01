; COMMAND-LINE: --produce-proofs
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(push)
(assert (= "A" ""))
(check-sat)
(pop)
(assert (= "" "A"))
(check-sat)
