; COMMAND-LINE: --strings-exp --re-elim=on
; EXPECT: unsat
(set-logic ALL)
(declare-const a String)
(assert (str.in_re a (re.++ (str.to_re "A") re.allchar (str.to_re "A"))))
(assert (not (str.in_re a (re.++ (str.to_re "A") (re.* (re.++ (str.to_re "A") re.allchar)) re.allchar (str.to_re "A")))))
(check-sat)
