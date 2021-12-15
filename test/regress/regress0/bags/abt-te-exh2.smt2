; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun p ((Bag Atom) (Bag Atom)) (Bag Atom))
(declare-fun j ((Bag Atom) (Bag Atom)) (Bag Atom))
(declare-fun k ((Bag Atom) (Bag Atom)) (Bag Atom))
(declare-fun d ((Bag Atom) (Bag Atom)) (Bag Atom))

(declare-fun a () (Bag Atom))
(declare-fun n () Atom)
(declare-fun v () Atom)

(assert (forall ((b Atom) (c Atom)) 
(or 
(>= (bag.count v (k (bag n 1) (j (bag b 1) a))) 1)
(= (as bag.empty (Bag Atom)) (d (j (bag b 1) a) (bag n 1)))
)
)
)

(check-sat)

