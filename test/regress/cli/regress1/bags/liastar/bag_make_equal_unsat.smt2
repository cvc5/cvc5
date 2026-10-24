; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)
; equal elements make the union max (bag x 3), of cardinality 3, and distinct
; elements make it of cardinality 2 + 3, so neither branch is satisfiable.
; Both cases are under a disjunction, so neither element equality can be
; propagated away, and the first branch needs the star to know that two
; constructed bags on the same element sit on the same summand.
(assert (let ((u (bag.union_max (bag x 2) (bag y 3))))
  (or (and (= x y) (= (bag.card u) 5))
      (and (not (= x y)) (= (bag.card u) 4)))))
(check-sat)
