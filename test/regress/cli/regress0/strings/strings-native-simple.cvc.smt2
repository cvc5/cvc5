; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ "abcd" y)))
(assert (>= (str.len x) 6))
(assert (< (str.len y) 5))
(check-sat)
