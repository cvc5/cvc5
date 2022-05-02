(set-logic QF_UFLIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(declare-fun d () Int)
(assert
(or (= c (f d)) (= d (f d)))
)
(check-sat)
