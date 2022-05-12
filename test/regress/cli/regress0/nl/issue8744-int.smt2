; COMMAND-LINE: -q
; EXPECT: sat
(set-logic NIRA)
(declare-const x Bool)
(declare-fun v () Int)
(declare-fun r () Int)
(assert (forall ((a Int)) (= (< v r) (= (= 0.0 (/ r v)) (distinct x (> (- r) 1))))))
(check-sat)
