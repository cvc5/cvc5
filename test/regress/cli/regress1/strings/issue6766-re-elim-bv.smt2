; COMMAND-LINE: --strings-exp --re-elim=agg
; EXPECT: sat
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(assert
 (str.in_re (str.++ a (ite (str.in_re (str.++ a "BA" b) (re.++ (re.* (str.to_re "A")) (str.to_re "B"))) b a))
  (re.diff (re.* (str.to_re "A")) (str.to_re ""))))
(check-sat)
