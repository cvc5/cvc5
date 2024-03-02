; COMMAND-LINE: --strings-exp
;EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun a () (Seq Int))
(declare-fun b () (Seq Int))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (or (= x z) (= y z)))
(assert (not (= (seq.nth a x) (seq.nth a z))))
(assert (not (= (seq.nth b y) (seq.nth b z))))
(check-sat)
