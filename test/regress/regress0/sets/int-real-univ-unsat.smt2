; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun a () (Set Real))

(declare-fun x () Real)

(assert (= (as univset (Set Real)) (as univset (Set Int))))

(assert (member x a))

(assert (and (<= 5.5 x) (< x 5.8)))

(check-sat)
