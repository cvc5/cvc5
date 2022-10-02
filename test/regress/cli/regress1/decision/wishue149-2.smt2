; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-logic AUFLIA)
(declare-const v4 Bool)
(declare-const v6 Bool)
(declare-const arr0 (Array Bool Int))
(declare-const arr1 (Array Bool (Array Bool Int)))
(assert (= (store arr1 v6 (store arr0 true 0)) (store arr1 true (store (store (store arr0 true 0) v4 0) true 96)) arr1 arr1))
(check-sat)
