; COMMAND-LINE: --strings-exp --seq-array=eager
(set-logic QF_SLIA)

(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))
(declare-fun z () (Seq Int))
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun i () Int)

(assert (= (seq.++ (seq.unit a) z) (seq.update x 0 (seq.unit b))))
(assert (not (= a b)))

(set-info :status unsat)
(check-sat)
