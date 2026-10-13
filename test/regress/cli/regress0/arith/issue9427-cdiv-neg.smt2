; EXPECT: unsat
(set-logic AUFBVFPDTNIRA)

(declare-const x Int)
(declare-const y Int)

(define-fun cdiv ((x Int) (y Int)) Int
  (ite (or (< 0 x) (= (mod x y) 0))
    (div x y)
    (ite (< 0 y)
      (+ (div x y) 1)
      (- (div x y) 1))))

(assert (not (= y 0)))
(assert (not (= (cdiv (- x) y) (- (cdiv x y)))))

(check-sat)