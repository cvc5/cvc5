; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)


(assert (or (= x 5) (= x 7) (= x 9)))

(assert (or (= y (+ x 1)) (= y (+ x 2))))

(assert (or (= z (+ y 5)) (= z (+ y 10))))

(assert (> (* z z) 1000000000))

(check-sat)
