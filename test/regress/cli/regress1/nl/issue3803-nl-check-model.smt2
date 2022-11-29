; COMMAND-LINE: --ext-rew-prep=use -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(declare-fun e () Real)
(assert (exists ((f Real)) (and (or (> (+ d (* (/ (* c e) (- (* c e) e)) f)) 0.0 (/ 0.0 a))) (> e 6.0))))
(assert (distinct a (/ b e)))
(check-sat)
