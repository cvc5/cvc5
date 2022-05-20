; EXPECT: (error "Term of kind int.pow2 requires the logic to include non-linear arithmetic")
; EXIT: 1
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (- x y) (int.pow2 x)))
(check-sat)
