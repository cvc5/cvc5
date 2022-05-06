; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-datatypes
 ((Datatype 0))
 (((constructor1 (selector1 Real))
    (constructor2 (selector2 Real) (selector3 Real) (selector4 Bool) (selector5 Real)))))

(assert
 (= 0
    (to_int
     (selector1 (constructor2 (sin (ite false (arcsin 0.0) 1.0)) 0.0 false 0.0)))))

(check-sat)
