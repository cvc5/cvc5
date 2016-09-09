(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)

(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const x7 Int)

(declare-const a1 Int)
(declare-const a2 Int)

(assert (and 
(sep (pto x1 a1) (pto x2 a2) (pto x4 a2) (pto x5 a2) (pto x6 a2) (pto x7 a2))
(sep (pto x1 a1) (pto x3 a2))
))

(assert (distinct x3 x2 x4 x5 x6 x7))

(check-sat)
