; COMMAND-LINE: --incremental --strings-exp --seq-array=eager
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe

(set-logic QF_SLIA)
(set-info :status unsat)

(declare-fun A () (Seq Int))
(declare-fun S1 () (Seq Int))
(declare-fun i () Int)

(assert (<= 0 i))
(assert (< i (- (seq.len A) 1)))
(assert (= S1 (seq.extract A i 1)))
(assert (distinct (seq.nth S1 0) (seq.nth A i)))
(check-sat)
