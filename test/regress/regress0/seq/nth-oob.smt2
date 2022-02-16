; COMMAND-LINE: --strings-exp --seq-array=lazy
; EXPECT: unsat

(set-logic QF_SLIA)
(declare-const x (Seq Int))
(declare-const i Int)
(declare-const j Int)
(declare-const v Int)
(assert (not (= (seq.nth (seq.update x i (seq.unit v)) j) (seq.nth x j))))
(assert (< i 0))
(assert (< j 0))
(check-sat)
