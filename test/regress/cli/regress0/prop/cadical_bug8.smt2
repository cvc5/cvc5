; COMMAND-LINE: --sat-solver=cadical
; EXPECT: sat
(set-logic QF_AUFLIA)
(set-info :status sat)
(declare-fun a () (Array Int Int))
(declare-fun e () Int)
(declare-fun i () Int)
(declare-fun i1 () Int)
(declare-fun s ((Array Int Int) (Array Int Int)) Int)
(assert (distinct 0 i1))
(assert (distinct (select (store a 0 e) (s a (store (store (store (store a 0 0) i 0) 0 0) 1 0))) (select (store (store (store a 0 e) 1 0) i1 0) (s a (store (store (store (store a 0 0) i 0) 0 0) 1 0)))))
(check-sat)
