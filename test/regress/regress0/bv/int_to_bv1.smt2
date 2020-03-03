;COMMAND-LINE: --solve-int-as-bv=64
;EXPECT: sat
(set-logic QF_UFNIA)
(declare-fun WnRElIU_new () Int)
(declare-fun shifted1_a__4 () Int)
(declare-fun shifted2_lam3n3 () Int)
(declare-fun F (Int) Int)
(assert (= (F shifted2_lam3n3) (+ WnRElIU_new shifted1_a__4)))
(check-sat)
