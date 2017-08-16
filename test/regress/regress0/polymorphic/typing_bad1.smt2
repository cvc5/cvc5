; COMMAND-LINE: --quant-polymorphic
(set-logic UF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(declare-sort A 1)
(declare-sort I1 0)
(declare-sort I2 0)
(declare-fun i1 () I1)

(declare-fun mk  (par (a) (a) (A a)))
(declare-fun get (par (a) ((A a)) a))

(assert (forall ((x I1)) (= x (get (as (mk x) (A I2))))))
(assert (not (= i1 (get (mk i1)))))

(check-sat)
(exit)

; EXPECT: (error "Parse Error: typing_bad1.smt2:13.53: Type ascription not satisfied.")
; EXIT: 1
