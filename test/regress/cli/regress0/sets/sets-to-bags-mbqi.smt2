; COMMAND-LINE: --sets-to-bags=setof --mbqi
; EXPECT: sat
; The subsolver of MBQI inherits --sets-to-bags and requires models.
(set-logic ALL)
(declare-fun A () (Set Int))
(declare-fun f (Int) Int)
(assert (set.member 1 A))
(assert (forall ((x Int)) (=> (set.member x A) (> (f x) x))))
(check-sat)
