; COMMAND-LINE: --mbqi -q
; EXPECT: sat
(set-logic ALL)
(assert (= (re.union (str.to_re "A") (str.to_re "B")) (re.union (str.to_re "B") (str.to_re "A"))))
(check-sat)
