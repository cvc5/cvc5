; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun p ((Set Atom) (Set Atom)) (Set Atom))
(declare-fun j ((Set Atom) (Set Atom)) (Set Atom))
(declare-fun k ((Set Atom) (Set Atom)) (Set Atom))
(declare-fun d ((Set Atom) (Set Atom)) (Set Atom))

(declare-fun a () (Set Atom))
(declare-fun n () Atom)
(declare-fun v () Atom)

(assert (forall ((b Atom) (c Atom)) 
(or 
(member v (k (singleton n) (j (singleton b) a)))
(= (as emptyset (Set Atom)) (d (j (singleton b) a) (singleton n)))
)
)
)

(check-sat)

