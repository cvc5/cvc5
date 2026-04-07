; COMMAND-LINE: --tc-mode=model-based
; EXPECT: unsat
(set-logic ALL)
(declare-fun s (Int) Int)
(assert (= (s 1) (+ 1 (s 0))))
(assert (= 1 (s (+ 1 (s 0)))))
(assert (= 0 (s 1)))
(check-sat)
