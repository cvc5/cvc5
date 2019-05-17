(set-info :smt-lib-version 2.5)
(set-logic ALL)
(set-info :status sat)
(set-option :strings-exp true)
(declare-fun x () Int)
(declare-fun y () String)
(declare-fun z () String)

(assert (str.contains "ABCD" (str.++ y (int.to.str x) z)))

(check-sat)
