; COMMAND-LINE: --incremental --strings-exp --seq-array=lazy
; EXPECT: sat

(set-logic ALL)
(set-info :status sat)

(declare-fun a () (Seq Int))
(declare-fun v () (Seq Int))

(declare-fun i () Int)

(declare-fun e () Int)
(declare-fun e2 () Int)

(assert (> i 0))
(assert (< i (seq.len a)))

(assert (= v (seq.update a 0 (seq.unit 1))))
(assert (not (= v a)))

(check-sat)
