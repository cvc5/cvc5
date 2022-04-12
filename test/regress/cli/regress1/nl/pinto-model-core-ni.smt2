; COMMAND-LINE: --nl-ext-tplanes --produce-models --model-core=non-implied
; EXPECT: sat
(set-logic ALL)
(declare-fun i1 () Real)
(declare-fun i2 () Real)
(declare-fun n () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun i11 () Real)
(declare-fun i21 () Real)

(assert (>= n 1))
(assert (and (<= 1 x)(<= x n)))
(assert (and (<= 1 y)(<= y n)))
(assert (or (= (/ (to_real (* (- 1) x)) (to_real n)) i1)(= i1 (/ (to_real x) (to_real n)))))
(assert (or (= (/ (to_real (* (- 1) y)) (to_real n)) i2)(= i2 (/ (to_real y) (to_real n)))))

(assert (and (= i1 i11) (= i2 i21) ))

(assert (not (and (or (= (- 1.0) i11 )(= i11 1.0)) (or (= (- 1.0) i21)(= i21 1.0)) )))

(check-sat)
