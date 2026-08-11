; COMMAND-LINE: --distinct-elim-threshold=0 -o post-asserts --check-proofs
; COMMAND-LINE: --distinct-elim-threshold=12 -o post-asserts --check-proofs
; SCRUBBER: grep -o "distinct\|^unsat$"
; EXPECT: unsat
; The proof checker testers dump the proof to stdout, which the benchmark
; printed by -o post-asserts interferes with, hence we disable them here.
; DISABLE-TESTER: lfsc
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; The distinct below has more than 10 children, so it is not eliminated by the
; rewriter and only the distinct-elim pass removes it, as witnessed by the
; absence of distinct in the output of the pass. Either disjunct of the second
; assertion equates two of its arguments, hence the problem is unsat. Run with
; proof checking to exercise the DISTINCT_ELIM proof produced by the pass.
(set-logic QF_UFLIA)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun x7 () Int)
(declare-fun x8 () Int)
(declare-fun x9 () Int)
(declare-fun x10 () Int)
(declare-fun x11 () Int)
(declare-fun x12 () Int)
(assert (distinct x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
(assert (or (= x3 x9) (= x1 x2)))
(check-sat)
