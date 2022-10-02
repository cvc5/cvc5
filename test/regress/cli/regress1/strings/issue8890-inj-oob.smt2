; COMMAND-LINE: --strings-exp --mbqi --strings-fmf
; EXPECT: sat
(set-logic ALL)
(declare-fun b (Int) Bool)
(declare-fun v () String)
(declare-fun a () String)
(assert (or (b 0) (= 0 (ite (= 1 (str.len v)) 1 0))))
(assert (forall ((e String) (va Int)) (or (= va 0) (distinct 0 (ite (str.prefixof "-" a) (str.to_int (str.substr v 1 (str.len e))) (str.to_int e))))))
(check-sat)
