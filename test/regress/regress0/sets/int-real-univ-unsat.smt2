; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-fun a () (Set Real))

(declare-fun x () Real)

(assert (= (as univset (Set Real)) (as univset (Set Real))))

(assert (member x a))

(assert (and (<= 5.5 x) (< x 5.8)))

(check-sat)
