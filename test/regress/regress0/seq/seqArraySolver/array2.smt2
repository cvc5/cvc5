; COMMAND-LINE: --incremental --strings-exp --seq-array=eager
; EXPECT: unsat

(set-logic ALL)
(set-info :status unsat)

(declare-fun a () (Seq Int))
(declare-fun v () (Seq Int))

(declare-fun i () Int)

(declare-fun e () Int)
(declare-fun e2 () Int)

(assert (> i 0))
(assert (< i (seq.len a)))

(assert (= v (seq.update a 0 (seq.unit (seq.nth a 0)))))
(assert (= e (seq.nth v i)))
(assert (= e2 (seq.nth a i)))
(assert (not (= e e2)))

(check-sat)
