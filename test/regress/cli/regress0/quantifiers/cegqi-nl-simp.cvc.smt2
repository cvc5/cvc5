; COMMAND-LINE: --nl-rlv=none
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(check-sat-assuming ( (not (forall ((x Int)) (exists ((y Int)) (= (* x y) x)))) ))
