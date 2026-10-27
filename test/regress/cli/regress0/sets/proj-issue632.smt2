; EXPECT: sat
(set-logic ALL)
(declare-const x (Set Bool))
(declare-const x4 (Set Bool))
(check-sat-assuming ((distinct set.empty (set.union x x4))))
