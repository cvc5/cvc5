; COMMAND-LINE: --produce-models --model-u-print=dt
; EXPECT: sat
; EXPECT: (
; EXPECT: (declare-datatype U ((@U_0) (@U_1) (@U_2)))
; EXPECT: (define-fun a () U (as @U_0 U))
; EXPECT: (define-fun b () U (as @U_1 U))
; EXPECT: (define-fun c () U (as @U_2 U))
; EXPECT: )
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(assert (distinct a b c))
(check-sat)
(get-model)
