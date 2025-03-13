; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :incremental true)
(set-option :mbqi true)
(set-option :solve-real-as-int true)
(declare-sort u 0)
(declare-const x Int)
(declare-const _x (Set u))
(assert (or (set.is_singleton _x) (= x 0)))
(check-sat)
(check-sat-assuming ((= x 0)))
