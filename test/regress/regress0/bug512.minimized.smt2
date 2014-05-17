; COMMAND-LINE: --tlimit-per 1000
; EXPECT: unknown
(set-logic UF)
(declare-sort T 0)
(declare-fun bool_2_U (Bool) T)
(declare-fun U_2_bool (T) Bool)
(assert (forall ((x T)) (= (bool_2_U (U_2_bool x)) x)))
(check-sat)
