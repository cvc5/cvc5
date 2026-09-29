; COMMAND-LINE: -o post-asserts
; SCRUBBER: grep -o "distinct x\|distinct y\|^sat$"
; EXPECT: distinct y
; EXPECT: sat
; Tests the default boundary of the rewriter, which eliminates (blasts)
; applications of distinct having at most 10 children into pairwise
; disequalities. The distinct over x1...x10 is thus eliminated, whereas the
; one over y1...y11 is retained. Note no threshold option is given here, so
; the distinct-elim preprocessing pass does not run.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x1 () U)
(declare-fun x2 () U)
(declare-fun x3 () U)
(declare-fun x4 () U)
(declare-fun x5 () U)
(declare-fun x6 () U)
(declare-fun x7 () U)
(declare-fun x8 () U)
(declare-fun x9 () U)
(declare-fun x10 () U)
(declare-fun y1 () U)
(declare-fun y2 () U)
(declare-fun y3 () U)
(declare-fun y4 () U)
(declare-fun y5 () U)
(declare-fun y6 () U)
(declare-fun y7 () U)
(declare-fun y8 () U)
(declare-fun y9 () U)
(declare-fun y10 () U)
(declare-fun y11 () U)
(assert (distinct x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))
(assert (distinct y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11))
(check-sat)
