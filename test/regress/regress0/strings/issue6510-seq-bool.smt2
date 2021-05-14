; COMMAND-LINE: --strings-exp -q
; EXPECT: sat
(set-logic ALL)
(declare-fun e () (Seq Bool))
(assert (seq.nth (ite (= 0 (seq.len e)) (as seq.empty (Seq Bool)) (seq.unit false)) 0))
(check-sat)
