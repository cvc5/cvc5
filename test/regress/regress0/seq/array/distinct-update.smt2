; COMMAND-LINE: --strings-exp --seq-array=eager
(set-logic QF_SLIA)

(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))
(declare-fun z () (Seq Int))
(declare-fun a () Int)
(declare-fun b () Int)

(assert (= y (seq.update x 0 (seq.unit a))))

(assert (= z (seq.update x 0 (seq.unit b))))

(assert (not (= a b)))
(assert (= y z))
(assert (> (str.len y) 0))

(set-info :status unsat)
(check-sat)
