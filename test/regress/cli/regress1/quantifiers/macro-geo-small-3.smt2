; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-sort U 0)
(declare-fun T (U U) Bool)
(define-fun P ((x1 U) (y1 U)) Bool (forall ((z1 U)) (or (not (T z1 x1)) (T z1 y1))))
(define-fun E ((y2 U)) Bool (forall ((z2 U) (w2 U)) (or (not (P z2 y2)) (P z2 w2) (P w2 z2))))
(assert (forall ((x3 U)) (exists ((y3 U)) (and (T y3 x3) (not (E x3))))))
; benchmark triggered unsoundness due to reusing a bound variable for prenexing the lifting of P twice within the definition of E
(check-sat)
