; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :incremental true)
(declare-fun x () (Array Int (Array Int Int)))
(assert (= (select (select x 0) 0) (select (select x 1) 1)))
(check-sat)
(assert (= x (store x 0 (select x 1))))
(check-sat)
