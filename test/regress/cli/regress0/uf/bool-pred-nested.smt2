(set-logic QF_UF)
(set-info :status sat)
(declare-fun P (Bool Bool) Bool)

(assert (P (P true (P false false)) (P false true)))

(check-sat)
