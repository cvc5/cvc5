; COMMAND-LINE: --strings-fmf
; EXPECT: sat
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(assert (distinct b (str.++ a a)))
(assert (str.in_re (str.++ b "\x2f" b) (re.++ (re.opt re.allchar) (str.to_re "\x2f\x65") re.all)))
(check-sat)
