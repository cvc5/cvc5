(set-info :smt-lib-version 2.5)
(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)

(assert (str.in.re x (re.loop (str.to.re "a") 5)))
(assert (str.in.re y (re.loop (str.to.re "b") 2 5)))
(assert (str.in.re z (re.loop (str.to.re "c") 5)))
(assert (> (str.len z) 7))
(assert (str.in.re w (re.loop (str.to.re "b") 2 7)))
(assert (> (str.len w) 2))
(assert (< (str.len w) 5))

(check-sat)
