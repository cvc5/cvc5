(set-logic QF_LRA)
(set-info :status sat)
(declare-fun v0 () Real)
(assert
   (= (>= v0 5) (< v0 0))
 )
(check-sat)
(exit)
