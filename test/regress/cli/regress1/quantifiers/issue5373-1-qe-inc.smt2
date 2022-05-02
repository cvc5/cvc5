; COMMAND-LINE: -i
; EXPECT: true
; EXPECT: true
(set-logic ALL)
(get-qe (exists ((q Real) (q Bool) (q Bool) (q Bool) (q Real) (q Real) (q Real)) true))
(get-qe (exists ((q Real) (q Bool) (f Bool) (q Bool) (q Real) (q Real) (q Real)) true))
