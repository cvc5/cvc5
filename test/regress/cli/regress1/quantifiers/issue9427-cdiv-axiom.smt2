; EXPECT: unsat
(set-logic AUFBVFPDTNIRA)

(declare-const x Int)
(declare-const y Int)

(declare-fun cdiv (Int Int) Int)

(assert
  (forall ((x Int) (y Int))
    (! (=> (not (= y 0)) (= (cdiv x y)
  (ite (or (< 0 x) (= (mod x y) 0))
    (div x y)
    (ite (< 0 y)
      (+ (div x y) 1)
      (- (div x y) 1))))) :pattern ((cdiv x y)))))

(assert (not (= y 0)))
(assert (not (= (abs (cdiv x y)) (cdiv (abs x) (abs y)))))

(check-sat)