; EXPECT: unsat
(set-logic ALL)
(declare-const x (Array Bool Bool))
(declare-const x4 (Array Bool (Array Bool Bool)))
(assert false)
(assert (not (set.subset (set.singleton x4) (set.singleton (store x4 (select (store x false false) false) x)))))
(check-sat)
