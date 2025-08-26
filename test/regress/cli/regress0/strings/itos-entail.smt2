(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)

(declare-fun x () Int)
(declare-fun y () String)
(declare-fun z () String)

(assert (str.contains "ABCD" (str.++ y (str.from_int x) z)))

(check-sat)
