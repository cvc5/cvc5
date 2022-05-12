; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)


(assert (> z 0))
(assert (> x y))

;(assert (not (> (* x z) (* y z))))
(assert (< (* x z) (* y z)))


(check-sat)
