; EXPECT: unsat

(set-option :strings-exp true)
(set-logic ALL)

(assert (forall ((x (Seq Int)) (xx (Seq Int)) ) (=> (and (= (seq.len x) (seq.len xx)) (forall ((i Int) )   (=> (and (<= 0 i) (< i (seq.len x))) (= (seq.nth x i) (seq.nth xx i))))) (= x xx))))

(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))

(assert (not (=> (= (seq.len x) (seq.len y)) (=> (forall ((i Int) )   (=> (and (<= 0 i) (< i (seq.len x))) (= (seq.nth x i) (seq.nth y i)))) (= x y)))))

(check-sat)
