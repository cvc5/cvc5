; COMMAND-LINE: --lang=smt2.6
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)

(assert (= x (str.replace_all "AABAABBC" "B" "def")))
(assert (= y (str.replace_all "AABAABBC" "AB" "BA")))

(check-sat)
