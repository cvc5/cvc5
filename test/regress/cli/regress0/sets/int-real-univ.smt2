; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-fun a () (Set Real))

(declare-fun x () Real)

(assert (= (as set.universe (Set Real)) (as set.universe (Set Real))))

(assert (set.member x a))

(assert (and (<= 5.5 x) (< x 6.1)))

(check-sat)
