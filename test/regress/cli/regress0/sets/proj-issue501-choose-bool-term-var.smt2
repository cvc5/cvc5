; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-option :sets-ext true)
(set-option :fmf-bound true)
(declare-const x (Bag (Set Bool)))
(declare-const x1 (Set Bool))
(declare-const x3 (Set Bool))
(declare-const x6 (Set Bool))
(assert (set.choose (ite (set.is_singleton x3) x6 x1)))
(assert (<= (set.card x6) (bag.count x6 x)))
(check-sat)
