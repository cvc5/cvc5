; EXPECT: unsat
(set-option :proof-elim-subtypes true)
(set-logic NIRA)
(declare-const x Int)
(declare-const y Int)
(assert (distinct (<= x y) (<= (to_real x) (to_real y))))
(check-sat)
