; EXPECT: unsat
(set-logic ALL)
(assert (or
(not (= (str.replace_re "BBBAAAAABAABA" (re.+ (str.to_re "A")) "C") "BBBCAAAABAABA"))
(not (= (str.indexof_re "BBBAAAAABAABA" (re.+ (str.to_re "A")) 0) 3))
(not (= (str.replace_re_all "BBBAAAAABAABA" (re.+ (str.to_re "A")) "C") "BBBCCCCCBCCBC"))
))
(check-sat)
