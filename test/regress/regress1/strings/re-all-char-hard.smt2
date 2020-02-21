; COMMAND-LINE: --no-re-elim
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)

; we should not intersect these two regular expressions
(assert (str.in.re x (re.++ (str.to.re "abc:def:ghi:") (re.* re.allchar ) (str.to.re ":") (re.* re.allchar ) (str.to.re ":cluster/sflower-bottle-guide-") (re.* re.allchar ))))
(assert (str.in.re x (re.++ (re.* re.allchar ) (str.to.re ":") (re.* re.allchar ) (str.to.re ":") (re.* re.allchar ) (str.to.re ":") (re.* re.allchar ) (str.to.re ":") (re.* re.allchar ) (str.to.re ":") (re.* re.allchar ))))
(check-sat)
