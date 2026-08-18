; COMMAND-LINE: --distinct-elim-threshold=12 -o post-asserts
; SCRUBBER: grep -o "distinct x\|distinct y\|^sat$"
; EXPECT: distinct y
; EXPECT: sat
; Tests the finite boundary of the distinct-elim preprocessing pass. Both
; distinct applications below have more than 10 children, hence neither is
; eliminated by the rewriter. The pass eliminates the one over x1...x12, which
; is within the threshold, and retains the one over y1...y13, which is not.
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
(declare-fun x11 () U)
(declare-fun x12 () U)
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
(declare-fun y12 () U)
(declare-fun y13 () U)
(assert (distinct x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
(assert (distinct y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13))
(check-sat)
