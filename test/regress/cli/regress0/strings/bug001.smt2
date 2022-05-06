(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (= "J" x))
(assert (= "j" y))

(assert (= "J" z))

(assert (= x z))

(check-sat)
