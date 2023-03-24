; COMMAND-LINE: --mbqi -q
; EXPECT: sat
(set-logic ALL)
(set-option :ieval use)
(declare-const x (Set Real))
(declare-const x5 Real)
(assert (set.is_singleton x))
(assert (not (set.is_singleton (set.minus x (set.singleton (- x5))))))
(check-sat)
