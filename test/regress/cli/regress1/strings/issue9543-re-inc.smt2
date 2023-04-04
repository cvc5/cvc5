; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic QF_S)
(declare-fun s () String)
(assert (distinct 0 (str.len s)))
(assert (not (str.in_re s (re.+ (re.range "0" "9")))))
(check-sat)
(assert (not (str.in_re s (re.+ (re.range "0" "f")))))
(check-sat)
