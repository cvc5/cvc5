; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (or (str.suffixof "B" x) (str.suffixof "AB" x)))
(assert (str.in_re (str.++ "A" x "B") (re.* (str.to_re "AB"))))
(check-sat)
