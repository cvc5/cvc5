(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun i () Int)

(assert (>= i 420))
(assert (= x (str.from_int i)))
(assert (= x (str.++ y "0" z)))
(assert (not (= y "")))
(assert (not (= z "")))



(check-sat)
