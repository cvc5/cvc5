; COMMAND-LINE: --strings-exp --seq-array=lazy
; EXPECT: sat
(set-logic QF_SLIA)
(declare-const x (Seq Int))
(declare-const i Int)
(declare-const j Int)
(assert (not (= (seq.nth (seq.update x i (seq.unit 5)) j) (seq.nth x j))))
(assert (< j 0))
(check-sat)
