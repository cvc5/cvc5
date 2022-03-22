; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () String)
(assert (str.in_re x (re.++ (re.opt (re.* (re.union (re.range "i" "j") (re.range "k" "l")))) (re.+ (str.to_re "abc")) ((_ re.loop 1 2) (str.to_re "def")) re.allchar )))
(assert (not (str.in_re x (re.inter (re.* re.allchar ) re.none ))))
(assert (= x "ikljabcabcdefe"))
(check-sat)
