(set-logic QF_LRA)
(set-info :status sat)

(declare-fun x () Real)
(declare-fun P () Bool)

(assert
 (let ((y (ite P 1.0 x)))
   (and (not (= y 1))
        (> y 0)
        (<= y 1))))

(check-sat)

(exit)
