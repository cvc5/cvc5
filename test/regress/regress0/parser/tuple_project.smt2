; EXPECT: (error "Parse Error: tuple_project.smt2:6.66: Invalid kind 'TUPLE_PROJECT', expected Terms with kind TUPLE_PROJECT must have at least 1 children and at most 1 children (the one under construction has 14)")
; EXIT: 1
(set-logic ALL)
(declare-fun z () (Tuple Int Int Int Int Int Int))
(declare-fun f () (Tuple Int Int Int))
(assert (= f ((_ tuple_project 0 1 2) z f f f f f f f f 0 0 0 0 0)))
(check-sat)
