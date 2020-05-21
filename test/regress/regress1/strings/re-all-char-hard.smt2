; COMMAND-LINE: --no-re-elim
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)

; we should not intersect these two regular expressions
(assert (str.in_re x (re.++ (str.to_re "abc:def:ghi:") (re.* re.allchar ) (str.to_re ":") (re.* re.allchar ) (str.to_re ":cluster/sflower-bottle-guide-") (re.* re.allchar ))))
(assert (str.in_re x (re.++ (re.* re.allchar ) (str.to_re ":") (re.* re.allchar ) (str.to_re ":") (re.* re.allchar ) (str.to_re ":") (re.* re.allchar ) (str.to_re ":") (re.* re.allchar ) (str.to_re ":") (re.* re.allchar ))))
(check-sat)
