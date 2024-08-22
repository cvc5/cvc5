; COMMAND-LINE: --strings-exp --seq-array=eager
; EXPECT: unsat
(set-logic ALL)
(declare-sort T 0)
(declare-fun t () T)
(declare-fun s (T) (Seq (Seq Int)))
(declare-fun u () (Seq Int))
(assert (= (seq.unit u) (s t)))
(assert (distinct u (seq.nth (s t) (- 1 (seq.len (s t))))))
(check-sat)
