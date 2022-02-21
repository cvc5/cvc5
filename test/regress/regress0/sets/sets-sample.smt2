; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(define-sort SetInt () (Set Int))

; Something simple to test parsing
(push 1)
(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun e () Int)
(assert (= a (set.singleton 5)))
(assert (= c (set.union a b) ))
(assert (not (= c (set.inter a b) )))
(assert (= c (set.minus a b) ))
(assert (set.subset a b))
(assert (set.member e c))
(assert (set.member e a))
(assert (set.member e (set.inter a b)))
(check-sat)
(pop 1)

; UF can tell that this is UNSAT (set.union)
(push 1)
(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(declare-fun z () (Set Int))
(assert (= x y))
(assert (not (= (set.union x z) (set.union y z))))
(check-sat)
(pop 1)

; UF can tell that this is UNSAT (containment)
(push 1)
(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(declare-fun e1 () Int)
(declare-fun e2 () Int)
(assert (= x y))
(assert (= e1 e2))
(assert (set.member e1 x))
(assert (not (set.member e2 y)))
(check-sat)
(pop 1)

; UF can tell that this is UNSAT (merge set.union + containment examples)
(push 1)
(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(declare-fun z () (Set Int))
(declare-fun e1 () Int)
(declare-fun e2 () Int)
(assert (= x y))
(assert (= e1 e2))
(assert (set.member e1 (set.union x z)))
(assert (not (set.member e2 (set.union y z))))
(check-sat)
(pop 1)

; test all the other kinds for completeness
(push 1)
(assert (set.member 5 (set.insert 1 2 3 4 (set.singleton 5))))
(assert (set.member 5 (set.insert 1 2 3 4 (as set.empty (Set Int)))))
(check-sat)
 
(exit) 
