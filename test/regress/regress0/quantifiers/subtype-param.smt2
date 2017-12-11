; COMMAND-LINE: --lang=smt2.5
; EXPECT: (error "argument type is not a subtype of the function's argument type:
; EXPECT: argument:  x
; EXPECT: has type:  (Array Int Int)
; EXPECT: not subtype: (Array Int Real)
; EXPECT: in term : (Q (as x (Array Int Real)))")
; EXIT: 1

(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-datatypes (T) ((List (cons (hd T) (tl (List T))) (nil))))

(declare-fun R ((List Real)) Bool)
(assert (forall ((x (List Real))) (R x)))

(declare-fun Q ((Array Int Real)) Bool)
(assert (forall ((x (Array Int Int))) (Q x)))

(declare-fun k1 () (List Int))
(declare-fun k2 () (Array Real Int))
(assert (or (not (R k1)) (not (Q k2))))

(check-sat)
