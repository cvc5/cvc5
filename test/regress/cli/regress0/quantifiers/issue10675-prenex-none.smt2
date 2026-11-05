; REQUIRES: unrestricted-mode
; COMMAND-LINE: --prenex-quant=none
; EXPECT: unsat
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(declare-sort integer 0)

;; "integer'int"
(declare-fun integerqtint (integer) Int)

;; "integer'axiom"
(assert
  (forall ((i integer))
    (and
      (<= (- 2147483648) (integerqtint i))
      (<= (integerqtint i) 2147483647))))

;; "in_range"
(define-fun in_range ((x Int)) Bool
  (and (<= (- 2147483648) x) (<= x 2147483647)))

;; "to_rep"
(define-fun to_rep ((x integer)) Int
  (integerqtint x))

;; "of_rep"
(declare-fun of_rep (Int) integer)

;; "inversion_axiom"
(assert
  (forall ((x integer)) (! (= (of_rep (to_rep x)) x) :pattern ((to_rep x)) )))

;; "range_axiom"
(assert
  (forall ((x integer)) (! (in_range (to_rep x)) :pattern ((to_rep x)) )))

;; "coerce_axiom"
(assert
  (forall ((x Int))
    (! (=> (in_range x) (= (to_rep (of_rep x)) x)) :pattern ((to_rep
                                                               (of_rep x))) )))

(declare-sort map1 0)

;; "has_bounds"
(declare-fun has_bounds (map1
  Int
  Int) Bool)

;; "get"
(declare-fun get (map1
  Int) integer)

;; "bool_eq"
(define-fun bool_eq ((a map1) (a__first Int) (a__last Int) (b map1) (b__first Int) (b__last Int)) Bool
  (ite (and
         (ite (<= a__first a__last)
           (and
             (<= b__first b__last)
             (= (- a__last a__first) (- b__last b__first)))
           (< b__last b__first))
         (forall ((temp___idx_168 Int))
           (=>
             (and (<= a__first temp___idx_168) (<= temp___idx_168 a__last))
             (= (to_rep (get a temp___idx_168)) (to_rep
                                                  (get
                                                    b
                                                    (+ (- b__first a__first) temp___idx_168)))))))
    true
    false))

;; "bool_eq_rev"
(assert
  (forall ((a map1) (b map1))
    (forall ((a__first Int) (a__last Int) (b__first Int) (b__last Int))
      (=>
        (= (bool_eq b b__first b__last a a__first a__last) true)
        (and
          (ite (<= a__first a__last)
            (and
              (<= b__first b__last)
              (= (- a__last a__first) (- b__last b__first)))
            (< b__last b__first))
          (forall ((temp___idx_168 Int))
            (=>
              (and (<= a__first temp___idx_168) (<= temp___idx_168 a__last))
              (= (to_rep (get a temp___idx_168)) (to_rep
                                                   (get
                                                     b
                                                     (+ (- b__first a__first) temp___idx_168)))))))))))

(declare-const b Int)

;; "temp_____aggregate_def_220"
(declare-fun temp_____aggregate_def_220 (Int) map1)

;; "def_axiom"
(assert
  (forall ((temp___219 Int))
    (! (let ((temp___221 (temp_____aggregate_def_220 temp___219)))
         (and
           (forall ((temp___222 Int))
             (! (=>
                  (and (<= 1 temp___222) (<= temp___222 1))
                  (=>
                    (in_range temp___219)
                    (= (to_rep (get temp___221 temp___222)) temp___219))) :pattern (
             (get
               temp___221
               temp___222)) ))
           (has_bounds temp___221 1 1))) :pattern ((temp_____aggregate_def_220
                                             temp___219)) )))

;; "def_axiom"
(assert
  (forall ((temp___219 Int))
     (!(let ((temp___221 (temp_____aggregate_def_220 temp___219)))
           (has_bounds temp___221 1 1)):pattern ((temp_____aggregate_def_220
                                             temp___219))) ))

;; Goal "def'vc"
;; File "arr_aggregate.ads", line 30, characters 0-0
(assert
  (not
  (forall ((one Int) (a map1))
    (=>
      (in_range one)
      (=>
        (has_bounds a 1 1)
        (=>
          (in_range b)
          (=>
            (= one 1)
            (forall ((a1 map1))
              (=>
                (and
                  (ite (= b 1)
                    (= (to_rep (get a1 one)) one)
                    (forall ((k Int))
                      (=>
                        (and (<= 1 k) (<= k 1))
                        (= (to_rep (get a1 k)) one))))
                  (has_bounds a1 1 1))
                (=>
                  (= b 1)
                  (= (bool_eq a1 1 1 (temp_____aggregate_def_220 one) 1 1) true)))))))))))

(check-sat)
