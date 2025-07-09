; COMMAND-LINE: --re-elim=on
; COMMAND-LINE: --re-elim=on --proof-cpc-str-in-re-nfa
; EXPECT: unsat
(set-logic ALL)
(declare-const a String)
(assert (str.in_re a (re.++ (str.to_re "A") re.allchar (str.to_re "A"))))
(assert (not (str.in_re a (re.++ (str.to_re "A") (re.* (re.++ (str.to_re "A") re.allchar)) re.allchar (str.to_re "A")))))
(check-sat)
