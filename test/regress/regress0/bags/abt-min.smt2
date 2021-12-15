; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun k (Atom Atom) (Bag Atom))

(declare-fun t0 () Atom)
(declare-fun t1 () Atom)
(declare-fun t2 () Atom)
(declare-fun v () Atom)
(declare-fun b2 () Atom)

(assert (forall ((b Atom)) (or 
(>= (bag.count v (k t0 b)) 1)
(>= (bag.count v (k t1 b)) 1)
) ))

(assert (not (>= (bag.count v (k t2 b2)) 1)))

(check-sat)

