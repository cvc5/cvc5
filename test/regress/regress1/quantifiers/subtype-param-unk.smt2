; COMMAND-LINE: --lang=smt2.5
; EXPECT: (error "argument type is not a subtype of the function's argument type:
; EXPECT: argument:  x
; EXPECT: has type:  (List Int)
; EXPECT: not subtype: (List Real)
; EXPECT: in term : (R (as x (List Real)))")
; EXIT: 1

; this will fail if type rule for APPLY_UF requires arguments to be subtypes
(set-logic ALL_SUPPORTED)

(declare-datatypes (T) ((List (cons (hd T) (tl (List T))) (nil))))

(declare-fun R ((List Real)) Bool)
(assert (forall ((x (List Int))) (R x)))
(declare-fun j1 () (List Real))
(assert (not (R j1)))

(declare-fun Q ((Array Int Real)) Bool)
(assert (forall ((x (Array Int Int))) (Q x)))
(declare-fun j2 () (Array Int Real))
(assert (not (Q j2)))

(check-sat)
