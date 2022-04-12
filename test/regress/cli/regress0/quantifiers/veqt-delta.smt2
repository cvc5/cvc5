; COMMAND-LINE: --relational-triggers
; EXPECT: unsat
(set-logic ALL)
(declare-sort S 0)
(declare-fun f () S)
(assert (forall ((? S)) (= ? f)))
(assert (exists ((? S) (v S)) (distinct ? v)))
(check-sat)
