; COMMAND-LINE: --mbqi
; EXPECT: unknown
(set-logic ALL)
(declare-const a (Array Int Int))
(assert (forall ((x (Array Int Int)) (i Int)) (not (= (store x i 0) a))))
(check-sat)
