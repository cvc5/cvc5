; COMMAND-LINE: --strings-exp --seq-array=lazy
; EXPECT: sat
(set-logic ALL)
(declare-sort S 0)
(declare-const x (Seq S))
(declare-const y (Seq S))
(declare-const y1 (Seq S))
(declare-const y2 (Seq S))
(declare-const i Int)
(declare-const a S)

(assert (= y (seq.update x i (seq.unit a))))
(assert (= y (seq.++ y1 y2)))
(assert (> (seq.len y1) 0))
(assert (> (seq.len y2) 0))

(check-sat)
