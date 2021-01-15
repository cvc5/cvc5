; COMMAND-LINE: --no-strings-lazy-pp -i
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun v6 () Bool)
(declare-fun str6 () String)
(assert (and v6 (str.in_re (str.replace str6 (str.from_int 12) str6) (str.to_re str6))))
(check-sat)
(check-sat)
(assert (not v6))
(check-sat)
