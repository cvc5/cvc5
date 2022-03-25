; COMMAND-LINE: --strings-exp --re-elim=agg
; EXPECT: sat
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(assert (str.in_re (str.replace_re b (str.to_re (str.replace_all a (str.++ b "a") b)) (str.++ b "a")) (re.+ (str.to_re "b"))))
(assert (str.in_re a (re.* (re.range "a" "b"))))
(check-sat)
