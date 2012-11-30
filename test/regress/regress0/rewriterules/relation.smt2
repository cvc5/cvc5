(set-logic AUFLIA)
(set-info :status unsat)

;; don't use a datatypes for currently focusing in uf
(declare-sort elt 0)

(declare-fun R (elt elt) Bool)

;; reflexive
(assert-rewrite ((x elt)) () () (R x x) true)

;; transitive
(assert-propagation ((x elt) (y elt) (z elt)) () () ((R x y) (R y z)) (R x z))

;; anti-symmetric
(assert-propagation ((x elt) (y elt)) () () ((R x y) (R y x)) (= x y))

(declare-fun e1 () elt)
(declare-fun e2 () elt)
(declare-fun e3 () elt)
(declare-fun e4 () elt)

(assert (not (=> (and (R e1 e2) (R e2 e3) (R e3 e4) (R e4 e1)) (= e1 e4))))

(check-sat)

(exit)