; COMMAND-LINE: --macros-quant
; EXPECT: (error "argument type is not a subtype of the function's argument type:
; EXPECT: argument:  x
; EXPECT: has type:  (List Int)
; EXPECT: not subtype: (List Real)
; EXPECT: in term : (R (as x (List Real)))")
; EXIT: 1

(set-logic ALL)

(declare-datatypes ((List 1)) ((par (T) ((cons (hd T) (tl (List T))) (nil)))))

(declare-fun R ((List Real)) Bool)
(assert (forall ((x (List Int))) (R x)))
(declare-fun j1 () (List Real))
(assert (not (R j1)))

(declare-fun Q ((Array Int Real)) Bool)
(assert (forall ((x (Array Real Int))) (Q x)))
(declare-fun j2 () (Array Real Real))
(assert (not (Q j2)))

(check-sat)
