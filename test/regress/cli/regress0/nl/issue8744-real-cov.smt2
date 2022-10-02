; REQUIRES: poly
; COMMAND-LINE: -q --nl-cov
; EXPECT: sat
(set-logic NIRA)
(declare-const x Bool)
(declare-fun v () Real)
(declare-fun r () Real)
(assert (forall ((a Real)) (= (< v r) (= (= 0.0 (/ r v)) (distinct x (> (- r) 1))))))
(check-sat)
