; EXPECT: unsat
(set-logic ALL)
(declare-const n Int)
(assert (not
(str.in_re (str.from_int n) (re.* (re.range "0" "9")))
))
(check-sat)
