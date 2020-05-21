(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun i () Int)
(declare-fun s () String)

(assert (< 67 (str.to_int s)))
(assert (= (str.len s) 2))
(assert (not (= s "68")))

(check-sat)
