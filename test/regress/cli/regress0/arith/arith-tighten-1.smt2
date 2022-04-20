; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_LIRA)

(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun x () Real)
(declare-fun y () Real)



(assert (= x y))
(assert (= x (- 2.5 y)))
(assert (>= (to_real (+ i j)) x))
(assert (<= (to_real j) (+ x 0.5)))
(assert (<= i 0))

(check-sat)

