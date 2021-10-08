; EXPECT: unsat
(set-logic ALL)
(set-option :incremental true)
(declare-fun all1 () (Array Int Int))
(declare-fun a () Int)
(declare-fun i () Int)
(assert (= all1 ((as const (Array Int Int)) 1)))
(assert (= a (select all1 i)))
(assert (not (= a 1)))
(push 1)

(assert true)

(check-sat)

(pop 1)

