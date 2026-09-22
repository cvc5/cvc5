; EXPECT: unsat
(set-logic ALL)
(declare-const p String)
(assert (str.in_re p (re.comp (re.* (re.union re.allchar (str.to_re "{5"))))))
(check-sat)
