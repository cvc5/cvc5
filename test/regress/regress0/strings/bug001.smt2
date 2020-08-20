(set-info :smt-lib-version 2.5)
(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (= "\x4a" x))
(assert (= "\x6a" y))

(assert (= "\x4A" z))

(assert (= x z))

(check-sat)
