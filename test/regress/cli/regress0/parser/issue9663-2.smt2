; DISABLE-TESTER: dump
; EXPECT: (error "expecting a single constant string term in regexp range")
; EXIT: 1
(set-logic QF_S)
(declare-fun a () String)
(assert (str.in_re a (re.diff (re.range "" "") (re.range "" "A"))))
(check-sat)
