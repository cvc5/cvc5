; EXPECT: unknown
(set-logic UFDTLIA)
(declare-datatypes ((U 0)) (((u) (w))))
(declare-fun f (Int) U)
(assert (forall ((s Int))
  (! (> s 0) :pattern ((is-u (f s)) (is-u (f s))))))
(check-sat)
