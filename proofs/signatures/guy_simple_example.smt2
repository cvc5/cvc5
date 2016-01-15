(set-logic QF_UF)

(declare-fun a () Bool)
(declare-fun b () Bool)

(assert (= a b))
(assert (not (= a b)))

(check-sat)
(exit)
