; COMMAND-LINE: --quant-polymorphic --no-check-proof
; EXPECT: unsat
(set-logic UF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort A 2)
(declare-sort I1 0)
(declare-sort I2 0)
(declare-fun i1 () I1)

(declare-fun mk  (par (a b) (a) (A a b)))
(declare-fun get (par (a b) ((A a b)) a))


(assert (forall ((x I1)) (= x (as (get (as (mk x) (A I1 I2))) I1))) )
(assert (not (= i1 (as (get (as (mk i1) (A I1 I2))) I1))))

(check-sat)
(exit)
