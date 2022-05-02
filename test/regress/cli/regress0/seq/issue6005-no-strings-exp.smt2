; EXPECT: (error "Term of kind seq.extract not supported in default mode, try --strings-exp")
; EXIT: 1
(set-logic ALL)
(declare-fun x () (Seq Int))
(assert (not (= x (seq.extract x 4 7))))
(check-sat)
