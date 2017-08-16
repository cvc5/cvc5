; COMMAND-LINE: --quant-polymorphic
(set-logic UF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(declare-sort A 1)
(declare-sort B 1)
(declare-sort I1 0)
(declare-sort I2 0)
(declare-fun i1 () I1)

(declare-fun mk  (par (a) (a) (A a)))
(declare-fun get (par (a) ((A a)) a))

(assert (forall ((x I1)) (= x (get (mk x) x))))
(assert (not (= i1 (get (mk i1)))))

(check-sat)
(exit)

; EXPECT: (error "Parse Error: typing_bad7.smt2:14.44: arity application mismatch")
; EXIT: 1
