; COMMAND-LINE: --no-jh-rlv-order
; EXPECT: unsat
(set-logic AUFBVFPDTNIRA)
(set-info :status unsat)
(set-info :smt-lib-version 2.6)

(declare-const dividend Int)
(declare-const divisor Int)

(define-fun pos_div_relation ((res Int) (num Int)
  (den Int)) Bool (let ((exact (div num den)))
                  (ite (= num 0) (= res 0)
                  (ite (= num (* exact den)) (= res exact)
                  (and (<= exact res) (<= res (+ exact 1)))))))

(declare-fun fxp_div_int (Int Int) Int)

(assert
  (forall ((x Int))
  (forall ((y Int))
  (! (ite (= x 0) (= (fxp_div_int x y) 0)
     (ite (and (< 0 x) (< 0 y)) (pos_div_relation (fxp_div_int x y) x y)
     (ite (and (< x 0) (< y 0)) (pos_div_relation (fxp_div_int x y) (- x)
     (- y))
     (ite (and (< x 0) (< 0 y)) (pos_div_relation (- (fxp_div_int x y)) (- x)
     y)
     (=> (and (< 0 x) (< y 0)) (pos_div_relation (- (fxp_div_int x y)) x
     (- y))))))) :pattern ((fxp_div_int x y)) ))))

(declare-fun of_int (Int) Int)

(declare-fun fxp_div (Int Int) Int)

;; VC was unprovable in the past when swapping the following two assertions
(assert
  (forall ((x Int))
  (! (ite (= x 0) (= (of_int x) 0)
     (ite (< 0 x) (pos_div_relation (of_int x) (* x 1073741824) 1)
     (pos_div_relation (- (of_int x)) (* (- x) 1073741824) 1))) :pattern (
  (of_int x)) )))

(assert
  (forall ((x Int))
  (forall ((y Int))
  (! (ite (= x 0) (= (fxp_div x y) 0)
     (ite (and (< 0 x) (< 0 y)) (pos_div_relation (fxp_div x y)
     (* (* (* x 1) 1073741824) 1073741824) (* (* (* y 1073741824) 1) 1))
     (ite (and (< x 0) (< y 0)) (pos_div_relation (fxp_div x y)
     (* (* (* (- x) 1) 1073741824) 1073741824)
     (* (* (* (- y) 1073741824) 1) 1))
     (ite (and (< x 0) (< 0 y)) (pos_div_relation (- (fxp_div x y))
     (* (* (* (- x) 1) 1073741824) 1073741824) (* (* (* y 1073741824) 1) 1))
     (=> (and (< 0 x) (< y 0)) (pos_div_relation (- (fxp_div x y))
     (* (* (* x 1) 1073741824) 1073741824) (* (* (* (- y) 1073741824) 1) 1))))))) :pattern (
  (fxp_div x y)) ))))

(define-fun in_range2 ((x Int)) Bool
  (and (<= (- 9223372036854775808) x) (<= x 9223372036854775807)))

(assert
  (not
  (=> (< 0 divisor)
  (=> (< divisor 2147483648)
  (=> (<= (- 2147483648) dividend)
  (=> (< dividend divisor)
  (in_range2 (fxp_div (of_int dividend) (of_int divisor)))))))))

(check-sat)
