; COMMAND-LINE: --enum-inst --mbqi
; EXPECT: unsat
(set-logic ALL)
(declare-fun r (Real) Int)
(assert (forall ((x Real) (i Int)) (= (> x (to_real i)) (= 0 (r x)))))
(check-sat)
