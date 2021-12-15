; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun j ((Bag Atom)) Atom)
(declare-fun kk (Atom (Bag Atom)) (Bag Atom))
(declare-fun n () (Bag Atom))

(assert (forall ((b Atom)) (= (as bag.empty (Bag Atom)) (kk (j (bag b 1)) n))))

(check-sat)

