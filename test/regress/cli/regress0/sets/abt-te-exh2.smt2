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
(set.member v (k (set.singleton n) (j (set.singleton b) a)))
(= (as set.empty (Set Atom)) (d (j (set.singleton b) a) (set.singleton n)))
)
)
)

(check-sat)

