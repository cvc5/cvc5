;; A new fast tableau-base ... Domenico Cantone et Calogero G.Zarba
(set-logic AUFLIA)
(set-info :status unsat)

(declare-sort elt1 0)
(declare-sort elt2 0)

(declare-fun g (elt2) Bool)

(declare-fun p (elt1 elt1) Bool)
(declare-fun f (elt2) elt1)
(declare-fun c1 () elt1)
(declare-fun c2 () elt1)

(assert (forall ((?e elt2)) (! (=> (g ?e) (= (f ?e) c2)) :rewrite-rule)))
(assert (forall ((?e elt2)) (! (=> (g ?e) (= (f ?e) c1)) :rewrite-rule)))

(declare-fun e () elt2)

(assert (not (=> (g e) (=> (p c1 c2) (p (f e) (f e)))) ))

(check-sat)

(exit)
