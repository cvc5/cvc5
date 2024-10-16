(set-logic ALL)
(set-info :status sat)
(set-option :dag-thresh 0)
(declare-const A (Set Int))
(assert (set.exists ((x Int)) A (set.exists ((y Int)) A (> x y))))
(check-sat)


