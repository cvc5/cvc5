; COMMAND-LINE: --quant-polymorphic --no-check-proofs
; EXPECT: unsat
(set-logic UFLRA)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort list 1)

(declare-sort unit 0)
(declare-fun  u    () unit)

(declare-fun nil (par (a) (unit) (list a)))
(declare-fun cons (par (a) (a (list a)) (list a)))

(assert (par (a) (forall ((x a)(l (list a))) (not (= (as (nil u) (list a)) (cons x l))))))

(declare-sort I1 0)
(declare-fun y1 () I1)
(declare-fun y2 () I1)
(declare-fun l2 () (list I1))

(assert (= (as (nil u) (list I1)) (cons y1 (cons y2 l2))))


(check-sat)
(exit)
