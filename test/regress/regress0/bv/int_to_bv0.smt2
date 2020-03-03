;COMMAND-LINE: --solve-int-as-bv=64
;EXPECT: sat
(set-logic QF_NIA)
(declare-fun WnRElIU_new () Int)
(declare-fun shifted1_a__4 () Int)
(declare-fun shifted2_lam3n3 () Int)
(assert (= shifted2_lam3n3 (div WnRElIU_new shifted1_a__4)))
(check-sat)
