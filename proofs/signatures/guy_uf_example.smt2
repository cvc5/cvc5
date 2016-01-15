(set-logic QF_UF)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)

(assert (= a b))
(assert (= b c))
(assert (not (= a c)))

(check-sat)
(exit)
