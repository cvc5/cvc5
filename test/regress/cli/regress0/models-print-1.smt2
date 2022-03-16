; the purpose of this test is to verify that there are no redundant `declare-fun`s

; EXIT: 0  
; SCRUBBER: grep declare-fun
(set-logic QF_UF)
(set-option :produce-models true)
(declare-sort Sort0 0)
(declare-fun f1 (Sort0) Bool)
(check-sat)
(get-model)
