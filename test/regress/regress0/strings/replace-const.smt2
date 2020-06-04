(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (= x (str.replace "AA" "AA" "def")))
(assert (= y (str.replace "BAA" "B" "def")))
(assert (= z (str.replace "AAB" "B" "def")))

(check-sat)
