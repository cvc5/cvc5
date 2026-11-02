; COMMAND-LINE: --sets-to-bags=relaxed
; EXPECT: unsat
; A set union is converted to a bag.setof of a bag union, hence A is a set.
(set-logic ALL)
(declare-fun A () (Set Int))
(declare-fun x () Int)
(assert (= (set.union A A) A))
(assert (set.member x (set.minus A (set.singleton x))))
(check-sat)
