; EXPECT: unsat
(set-logic ALL)

(declare-sort T 0)
(declare-sort U 0)
(declare-fun subtype (T T) Bool)
(declare-fun typeof (U) T)
(assert (forall ((t1 T) (t2 T)) (! (=> (and (subtype t1 t2) (subtype t2 t1)) (= t1 t2))
 :pattern ((subtype t1 t2) (subtype t2 t1)))))

(assert (! false :named L_1))

(check-sat)
