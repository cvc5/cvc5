; COMMAND-LINE: --incremental --strings-exp --seq-array=eager
; EXPECT: unsat

(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))
(declare-fun z () (Seq Int))
(declare-fun i () Int)
(declare-fun e () Int)

(assert (>= i 0))
(assert (< i (seq.len x)))

(assert (= 1 (seq.len x)))
(assert (= 1 (seq.len y)))

(assert (= e (seq.nth x i)))
(assert (= e (seq.nth y i)))

(assert (not (= x y)))

(check-sat)
(exit)
