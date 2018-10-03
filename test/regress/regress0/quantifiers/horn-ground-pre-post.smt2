; COMMAND-LINE: --sygus-inference
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)

(declare-fun I (Int Int) Bool)

(assert (I 1 0))

(assert (forall ((x Int) (y Int) (xp Int) (yp Int)) (=> (and (I x y) (= xp (+ x 1)) (= yp y)) (I xp yp))))

(assert (not (I 1 1)))

(check-sat)
