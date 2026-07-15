; COMMAND-LINE: --distinct-elim-threshold=0
; COMMAND-LINE: --distinct-elim-threshold=12
; EXPECT: sat
; Exercises the distinct-elim preprocessing pass, which eagerly blasts distinct
; terms with at most N children (0 means no limit) into pairwise disequalities.
; The distinct below has more than 10 children, so it is not eliminated by the
; rewriter and only the pass removes it. We therefore only use thresholds that
; are 0 or greater than 10.
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
(check-sat)
