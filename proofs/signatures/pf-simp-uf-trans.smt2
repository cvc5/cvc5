(set-logic QF_UF)

(declare-sort s 0)

(declare-fun a1 () s)
(declare-fun b1 () s)
(declare-fun a2 () s)
(declare-fun b2 () s)

(declare-fun f (s s) s)

(assert (= a1 b1))
(assert (= b1 b2))
(assert (not (= a1 b2)))

(check-sat)
(exit)