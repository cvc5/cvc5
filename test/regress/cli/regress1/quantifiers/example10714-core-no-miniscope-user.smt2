; EXPECT: unsat
(set-logic ALL)
(declare-sort integer 0)
(declare-datatypes ((t 0)) (((tqtmk (rec__first integer) (rec__last integer)))))
(declare-sort map1 0)
(declare-datatypes ((us_t 0)) (((us_tqtmk (elts map1) (rt t)))))
(define-fun in_range ((x Int)) Bool (and (<= (- 2147483648) x) (<= x 2147483647)))
(declare-fun to_array (us_t) map1)
(declare-fun get (map1 Int) integer)
(declare-fun to_rep (integer) Int)
(declare-fun last (us_t) Int)
(declare-fun first (us_t) Int)
(define-fun has_zero ((param__a us_t)) Bool (ite (exists ((temp___170 Int)) (and (and (<= (first param__a) temp___170) (<= temp___170 (last param__a))) (= (to_rep (get (to_array param__a) temp___170)) 0))) true false))
(declare-fun of_array (map1 Int Int) us_t)
(declare-fun find_first_zero (us_t) Int)
(declare-fun slice (map1 Int Int) map1)
(declare-fun in_range2 (Int) Bool)
(declare-fun mk (Int Int) t)

(declare-const a__first integer)

(declare-const a__last integer)

(declare-const a_old us_t)
(define-fun aa ((Test_declare__set_range_to_zero__a___a___ map1) (Test_declare__set_range_to_zero__fst_zero___fst_zero___ Int)) us_t
  (let ((temp___179 (let ((temp___178 (to_rep a__last)))
                      (let ((temp___176 (+ Test_declare__set_range_to_zero__fst_zero___fst_zero___ 1)))
                        (of_array
                          (slice (to_array a_old) temp___176 temp___178)
                          temp___176
                          temp___178)))))
    (let ((temp___180 (to_array temp___179)))
      (of_array temp___180 (first temp___179) (last temp___179)))))
(declare-const fst_zero2 Int)
(declare-const a2 map1)

(assert
  (forall ((param__a us_t))
    (! 
         (let ((result (find_first_zero param__a)))
           (and
             (and
               (and
                 (and
                   (<= (first param__a) result)
                   (<= result (last param__a)))
                 (= (to_rep (get (to_array param__a) result)) 0))
               (not
                 (= (has_zero
                            (of_array
                              (slice
                                (to_array param__a)
                                (first param__a)
                                (- result 1))
                              (first param__a)
                              (- result 1))) true)))
             (in_range2 result))) :pattern ((find_first_zero param__a)) )))

(assert (not 
         (let ((result (find_first_zero (aa a2 fst_zero2))))
           (and
             (and
               (and
                 (and
                   (<= (first (aa a2 fst_zero2)) result)
                   (<= result (last (aa a2 fst_zero2))))
                 (= (to_rep (get (to_array (aa a2 fst_zero2)) result)) 0))
               (not
                 (= (has_zero
                            (of_array
                              (slice
                                (to_array (aa a2 fst_zero2))
                                (first (aa a2 fst_zero2))
                                (- result 1))
                              (first (aa a2 fst_zero2))
                              (- result 1))) true)))
             (in_range2 result))) ))

(check-sat)
