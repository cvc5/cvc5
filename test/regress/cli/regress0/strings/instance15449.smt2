; EXPECT: unsat
(set-logic QF_S)
(declare-const X String)
(assert (not (str.in_re X (re.++ (re.union (re.comp (str.to_re "S")) (re.++ (str.to_re "S") (re.comp (str.to_re "E"))) (re.++ (str.to_re "SE") (re.comp (str.to_re "P")))) (re.* re.allchar) (str.to_re "\u{a}")))))
(assert (str.in_re X (str.to_re "Yeah!Host:EnTrYwww.ZSearchResults.com\u{13}\u{a}")))
(check-sat)
(exit)
