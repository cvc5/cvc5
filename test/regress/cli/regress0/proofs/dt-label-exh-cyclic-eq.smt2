; EXPECT: unsat
; Label exhaustion concludes (is C (unbox (box m))) from (not (is A m)),
; (not (is B (unbox (box m)))) and (= m (unbox (box m))). Its proof moves
; (not (is A m)) to (unbox (box m)) by congruence over the equality. Using the
; equality as the substitution m -> (unbox (box m)) does not work, since m occurs
; in (unbox (box m)), and hence the substitution also changes the target.
(set-logic UFDTLIA)
(declare-datatypes ((D 0)) (((A (a1 Int)) (B (b1 Int)) (C (c1 Int)))))
(declare-sort Poly 0)
(declare-fun box (D) Poly)
(declare-fun unbox (Poly) D)
(declare-fun p (D) Bool)
(declare-fun m () D)
(assert (forall ((x D)) (! (= x (unbox (box x))) :pattern ((box x)))))
(assert (not ((_ is A) m)))
(assert (not ((_ is B) (unbox (box m)))))
(assert (not (p m)))
(assert (p (C (c1 m))))
(check-sat)
