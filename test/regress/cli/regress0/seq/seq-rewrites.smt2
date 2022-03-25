(set-logic QF_UFSLIA)
(set-info :status unsat)
(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))
(declare-fun z () Int)

(assert 
(or

(not (=
(seq.replace (seq.++ (seq.unit 0) x) (seq.unit 1) (seq.unit 2))
(seq.++ (seq.unit 0) (seq.replace x (seq.unit 1) (seq.unit 2)))
))

(not (=
(seq.at (seq.++ x (seq.unit 14)) (seq.len x))
(seq.unit 14)
))

(not (=
(seq.at x z)
(seq.extract x z 1)
))

(not (=
(seq.contains (seq.++ x y) y)
true
))

(not (=
(seq.prefixof (seq.unit z) (seq.unit 4))
(seq.suffixof (seq.unit z) (seq.unit 4))
))

(not (=
(seq.rev (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)))
(seq.++ (seq.unit 3) (seq.unit 2) (seq.unit 1))
))

))



(check-sat)
