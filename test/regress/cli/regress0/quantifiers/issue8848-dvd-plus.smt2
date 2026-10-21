; EXPECT: unsat
(set-logic UFLIA)

(declare-fun dvd (Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (=> (dvd x y) (dvd x z) (dvd x (+ y z)))))

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(assert (dvd a b))
(assert (dvd a c))
(assert (dvd a d))
(assert (not (dvd a (+ b c d))))

(check-sat)
