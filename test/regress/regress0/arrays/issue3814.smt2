; REQUIRES: proof
; COMMAND-LINE: --produce-unsat-cores
; EXPECT: sat
(set-logic QF_AX)
(declare-fun a () (Array Bool Bool))
(declare-fun b () (Array Bool Bool))
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(assert (= a (store b c d)))
(assert (= e (select a (select b d))))
(check-sat)
