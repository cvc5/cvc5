; EXPECT: sat
(set-logic ALL)
(set-option :sets-ext true)
(set-option :ee-mode central)
(declare-const x (Set (_ BitVec 44)))
(assert (> (set.card x) (div (set.card x) (set.card x))))
(check-sat)
