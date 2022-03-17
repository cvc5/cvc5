; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun a () (Seq (Seq Int)))
(declare-fun b () (Seq (Seq Int)))
(declare-fun c () (Seq (Seq Int)))
(declare-fun d () (Seq (Seq Int)))
(declare-fun e () (Seq Int))
(declare-fun f () (Seq Int))
(assert (distinct a (seq.++ (seq.unit e) b)))
(assert (= (seq.++ (seq.unit f) d) a c))
(check-sat)
