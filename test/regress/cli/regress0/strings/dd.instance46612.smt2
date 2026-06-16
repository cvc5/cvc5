; COMMAND-LINE: --check-proofs-complete
; EXPECT: unsat
(set-logic ALL)
(declare-const X String)
(assert (str.in_re X (re.++ (str.to_re "2") (re.++ (re.* (re.range "0" "9")) ((_ re.loop 8 8) (re.range "0" "9"))))))
(assert (not (str.in_re X (re.++ (str.to_re "2") re.all))))
(check-sat)
