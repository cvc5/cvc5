; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-const X String)
(assert (str.in_re X (re.++ ((_ re.loop 2 3) (re.range "a" "z")) (re.++ (str.to_re ".") (re.range "A" "Z")) (re.range "A" "Z") (re.range "a" "z"))))
(assert (str.in_re X (re.++ (re.* re.allchar) (str.to_re "{0") (re.union (str.to_re "t") (str.to_re "f")) (str.to_re "tp"))))
(check-sat)
