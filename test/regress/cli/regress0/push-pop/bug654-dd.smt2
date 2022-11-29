; COMMAND-LINE: --incremental --fmf-fun --strings-exp
; DISABLE-TESTER: model
(set-logic ALL)
(declare-datatypes ((List_T_C 0) (T_CustomerType 0)) (
((List_T_C$CNil_T_CustomerType) (ListTC (ListTC$head T_CustomerType) (ListTC$tail List_T_C)))
((T_CustomerType$C_T_CustomerType (T_CustomerType$C_T_CustomerType$a_CompanyName Int) (T_CustomerType$C_T_CustomerType$a_ContactName Int) (ID Int)))
))
(declare-fun f (List_T_C) Bool)
(declare-fun tail_uf_1 (List_T_C) List_T_C)
(declare-fun head_uf_2 (List_T_C) T_CustomerType)
(declare-sort U 0)
(declare-fun a (U) List_T_C)
(declare-fun z (U) U)
(assert
(forall ((?i U))
(= (f (a ?i)) (not ((_ is ListTC) (a ?i)))
)))
(assert
(forall ((?i U))
(= (a (z ?i)) (tail_uf_1 (a ?i)))) )
; EXPECT: sat
(push 1)
(check-sat)
(pop 1)
; EXPECT: sat
(push 1)
(check-sat)
(pop 1)
