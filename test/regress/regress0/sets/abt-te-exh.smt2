; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun j ((Set Atom)) Atom)
(declare-fun kk (Atom (Set Atom)) (Set Atom))
(declare-fun n () (Set Atom))

(assert (forall ((b Atom)) (= (as emptyset (Set Atom)) (kk (j (singleton b)) n))))

(check-sat)

