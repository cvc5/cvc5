(set-logic QF_S)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun i () Int)
(declare-fun s () String)

(assert (< 67 (str.to.int s)))
(assert (= (str.len s) 2))
(assert (not (= s "68")))

(check-sat)
