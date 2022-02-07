; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-const y String)
(assert (= 2 (str.len y)))
(assert (str.in_re y (re.+ (re.range "!" "3"))))
(assert (str.contains "1kN" y))
(check-sat)
