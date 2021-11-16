; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
(set-option :incremental true)
(set-logic ALL)

(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(declare-fun z () (Set Int))
(declare-fun e1 () Int)
(declare-fun e2 () Int)
(push 1)
(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun e () Int)
(assert (= a (set.singleton 5)))
(assert (= c (set.union a b)))
(assert (not (= c (set.inter a b))))
(assert (= c (set.minus a b)))
(assert (set.subset a b))
(assert (set.member e c))
(assert (set.member e a))
(assert (set.member e (set.inter a b)))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(push 1)
(assert (= x y))
(assert (not (= (set.union x z) (set.union y z))))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(push 1)
(assert (= x y))
(assert (= e1 e2))
(assert (set.member e1 x))
(assert (not (set.member e2 y)))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(push 1)
(assert (= x y))
(assert (= e1 e2))
(assert (set.member e1 (set.union x z)))
(assert (not (set.member e2 (set.union y z))))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(push 1)
(assert (set.member 5 (set.union (set.union (set.union (set.union (set.singleton 1) (set.singleton 2)) (set.singleton 3)) (set.singleton 4)) (set.singleton 5))))
(assert (set.member 5 (set.union (set.union (set.union (set.union (set.singleton 1) (set.singleton 2)) (set.singleton 3)) (set.singleton 4)) (as set.empty (Set Int)))))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(check-sat-assuming ( (not (let ((_let_1 (set.member e1 z))) (and _let_1 (not _let_1)))) ))
