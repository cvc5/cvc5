; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun k (Atom Atom) (Set Atom))

(declare-fun t0 () Atom)
(declare-fun t1 () Atom)
(declare-fun t2 () Atom)
(declare-fun v () Atom)
(declare-fun b2 () Atom)

(assert (forall ((b Atom)) (or 
(set.member v (k t0 b))
(set.member v (k t1 b))
) ))

(assert (not (set.member v (k t2 b2))))

(check-sat)

