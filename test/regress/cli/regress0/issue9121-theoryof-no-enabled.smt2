; EXPECT: (error "The logic was specified as AUF, which doesn't include THEORY_DATATYPES, but got a preprocessing-time term for that theory.
; EXPECT: The term:
; EXPECT: (e x)")
; EXIT: 1
(set-logic AUF)
(declare-datatypes ((l 0) (t 0)) (
((n) (c (e t) (d l)))
((m (f l)))
))
(declare-fun x () l)
(declare-fun y () t)
(assert (distinct y (e x)))
(check-sat)
