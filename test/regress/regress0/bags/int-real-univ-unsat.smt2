; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-fun a () (Bag Real))

(declare-fun x () Real)

(assert (= (as set.universe (Bag Real)) (as set.universe (Bag Real))))

(assert (>= (bag.count x a) 1))

(assert (and (<= 5.5 x) (< x 5.8)))

(check-sat)
