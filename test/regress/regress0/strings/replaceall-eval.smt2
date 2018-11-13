(set-info :smt-lib-version 2.5)
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)

(assert (= x (str.replaceall "AABAABBC" "B" "def")))
(assert (= y (str.replaceall "AABAABBC" "AB" "BA")))

(check-sat)
