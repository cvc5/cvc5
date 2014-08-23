(set-logic UF)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(declare-sort A 1)
(declare-sort I1 0)
(declare-sort I2 0)
(declare-fun i1 () I1)

(declare-fun mk  (par (a) (a) (A a)))
(declare-fun get (par (a) ((A a)) a))

(assert (forall ((x I1)(y I2)) (= x (get (mk y)))))
(assert (not (= i1 (get (mk i1)))))

(check-sat)
(exit)

; EXPECT-ERROR: (error "Parse Error: typing_bad0.smt2:12.49: Subexpressions must have a common base type:
; EXPECT-ERROR: 
; EXPECT-ERROR:   (assert (forall ((x I1)(y I2)) (= x (get (mk y)))))
; EXPECT-ERROR:                                                ^
; EXPECT-ERROR: 
; EXPECT-ERROR: Equation: (= x (get (mk y)))
; EXPECT-ERROR: Type 1: I1
; EXPECT-ERROR: Type 2: I2
; EXPECT-ERROR: ")
; EXIT: 1
