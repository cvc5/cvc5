; COMMAND-LINE: --re-elim
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(assert (str.in_re a (re.++ re.allchar (str.to_re a) (re.* re.allchar))))
(check-sat)
