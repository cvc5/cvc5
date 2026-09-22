; EXPECT: unsat
(set-logic QF_S)
(declare-fun a () String)
(assert (str.in_re a (re.diff (re.range "" "") (re.range "" "A"))))
(check-sat)
