; COMMAND-LINE: --check-proofs-complete
; EXPECT: unsat
(set-logic ALL)
(declare-const X String)
(assert (str.in_re X (str.to_re "")))
(assert (str.in_re X (re.++ (re.* re.allchar) (re.opt (str.to_re "/")) (str.to_re "-"))))
(check-sat)
