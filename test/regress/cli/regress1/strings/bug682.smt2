; COMMAND-LINE: --incremental --strings-exp
(set-logic QF_S)

(declare-fun a () String)
(define-fun replace3 ((x String) (y String) (z String)) String (str.replace x y z) )

(push 1)
(assert (= (replace3 a "5" "3") "333"))
(assert (str.contains a "5"))
; EXPECT: sat
(check-sat)
(pop 1)

(push 1)
(assert (= (replace3 a "5" "3") "333"))
(assert (str.contains a "5"))
; EXPECT: sat
(check-sat)
(pop 1)
