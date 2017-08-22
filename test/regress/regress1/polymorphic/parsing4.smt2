; COMMAND-LINE: --quant-polymorphic --no-check-proofs
; EXPECT: unsat
(set-logic UF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort A 1)
(declare-sort I1 0)
(declare-fun i1 () I1)

(declare-fun mk  (par (a) (a) (A a)))
(declare-fun get (par (a) ((A a)) a))

(assert (par (a) (forall ((x a)) (= x (as (get (as (mk x) (A a))) a)))))
(assert (not (= i1 (as (get (as (mk i1) (A I1))) I1))))



(check-sat)
(exit)
