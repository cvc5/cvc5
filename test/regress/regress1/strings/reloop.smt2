(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)

(assert (str.in_re x ((_ re.^ 5) (str.to_re "a"))))
(assert (str.in_re y ((_ re.loop 2 5) (str.to_re "b"))))
(assert (str.in_re z ((_ re.loop 5 15) (str.to_re "c"))))
(assert (> (str.len z) 7))
(assert (str.in_re w ((_ re.loop  2 7) (str.to_re "b"))))
(assert (> (str.len w) 2))
(assert (< (str.len w) 5))

(check-sat)
