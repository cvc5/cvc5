(declare-fun c () Int)
(assert (= (> c 1) (= 6 (* c c))))
(check-sat)
