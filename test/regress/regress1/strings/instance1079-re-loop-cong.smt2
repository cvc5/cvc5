; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic QF_S)
(set-info :status unsat)
(declare-const X String)
(assert (not (str.in_re X (re.++ ((_ re.loop 0 16) (re.union re.allchar (str.to_re "\u{0a}"))) (str.to_re "\u{0a}")))))
(assert (str.in_re X (str.to_re "//cdmax/Ui\u{0a}")))
(check-sat)
