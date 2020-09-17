; COMMAND-LINE: --theoryof-mode=type --quiet --nl-ext-tplanes
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (and (= a (- 7 (* a a))) (>= (* 9 b) 7) (>= (* a b) 45)))
(assert (= b (* (div 7 c) (- 96 (div 45 b)))))
(set-info :status unsat)
(check-sat)
