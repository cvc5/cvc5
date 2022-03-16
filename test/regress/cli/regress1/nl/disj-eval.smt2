; COMMAND-LINE: --nl-ext=full
; EXPECT: sat
(set-logic QF_NIA)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (or (= x 5) (= x 7) (= x 9) (= x 27) (= x 10)))
(assert (or (= y 0) (= y 1) (= y 9) (= y 8)))


(assert (= (* x x) (* y y y)))

(check-sat)
