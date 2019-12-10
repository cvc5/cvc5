(set-logic QF_AUFLIRA)
(declare-fun a () (Array Int Real))

(assert (= a ((as const (Array Int Real)) 0.0)))

(check-sat)
