; EXPECT: sat
; EXPECT: (
; EXPECT: ; cardinality of U is 1
; EXPECT: ; rep: (as @U_0 U)
; EXPECT: (define-fun x () U (as @U_0 U))
; EXPECT: )
; EXPECT: ((as @U_0 U))
; EXPECT: (((_ fmf.card U 1) true))
; EXPECT: ((x (as @U_0 U)))

(set-option :produce-models true)

(set-logic UFC)

(declare-sort U 0)
(declare-const x U)
(assert (_ fmf.card U 1))

(check-sat)
(get-model)
(get-model-domain-elements U)
(get-value ((_ fmf.card U 1)))
(get-value (x))
