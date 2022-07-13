; COMMAND-LINE: --strings-exp --seq-array=lazy
; EXPECT: sat
(set-logic ALL)
(declare-sort S 0)
(declare-const x (Seq S))
(declare-const y (Seq S))
(declare-const y1 (Seq S))
(declare-const y2 (Seq S))
(declare-const x1 (Seq S))
(declare-const x2 (Seq S))
(declare-const i Int)
(declare-const a S)

(assert (= y (seq.update x i (seq.unit a))))
(assert (= y (seq.++ y1 y2)))
(assert (= x (seq.++ x1 x2)))
(assert (> (seq.len y1) 0))
(assert (> (seq.len y2) 0))
(assert (> (seq.len x1) 0))
(assert (> (seq.len x2) 0))
(assert (<= 0 i))
(assert (< i (seq.len x)))

(check-sat)
