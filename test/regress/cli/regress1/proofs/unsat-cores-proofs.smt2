; COMMAND-LINE: --produce-proofs -i
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(push)
(assert (= "A" ""))
(check-sat)
(pop)
(assert (= "" "A"))
(check-sat)
