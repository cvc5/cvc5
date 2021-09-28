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
(assert (= a (singleton 5)))
(assert (= c (union a b)))
(assert (not (= c (intersection a b))))
(assert (= c (setminus a b)))
(assert (subset a b))
(assert (member e c))
(assert (member e a))
(assert (member e (intersection a b)))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(push 1)
(assert (= x y))
(assert (not (= (union x z) (union y z))))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(push 1)
(assert (= x y))
(assert (= e1 e2))
(assert (member e1 x))
(assert (not (member e2 y)))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(push 1)
(assert (= x y))
(assert (= e1 e2))
(assert (member e1 (union x z)))
(assert (not (member e2 (union y z))))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(push 1)
(assert (member 5 (union (union (union (union (singleton 1) (singleton 2)) (singleton 3)) (singleton 4)) (singleton 5))))
(assert (member 5 (union (union (union (union (singleton 1) (singleton 2)) (singleton 3)) (singleton 4)) (as emptyset (Set Int)))))
(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)
(check-sat-assuming ( (not (let ((_let_1 (member e1 z))) (and _let_1 (not _let_1)))) ))
