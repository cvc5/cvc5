; COMMAND-LINE: --strings-exp --seq-array=lazy
; EXPECT: unsat

(set-logic QF_SLIA)

(declare-fun A () (Seq Int))
(declare-fun i () Int)
(declare-fun S () (Seq Int))
(declare-fun B () (Seq Int))

(assert (<= 0 i))
(assert (< i (- (seq.len A) 1)))
(assert (= S (seq.extract A i 1)))
(assert (= (seq.nth A i) (seq.nth A (+ i 1))))

(assert (= B (seq.update A (+ i 1) S)))
(assert (distinct (seq.nth B (+ i 1)) (seq.nth S 0)))
(check-sat)
