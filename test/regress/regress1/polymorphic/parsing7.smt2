; COMMAND-LINE: --quant-polymorphic --no-check-proofs
; EXPECT: unsat
(set-logic UFLRA)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort list 1)

(declare-fun nil (par (a) () (list a)))
(declare-fun cons (par (a) (a (list a)) (list a)))
(declare-fun length (par (a) ((list a)) Real))

(assert (par (a) (= (length (as nil (list a))) 0)))
(assert (par (a) (forall ((x a)(l (list a))) (= (length (cons x l)) (+ 1 (length l))))))

(declare-sort I1 0)
(declare-fun y1 () I1)
(declare-fun y2 () I1)


(assert (not (= (length (cons y1 (cons y2 (as nil (list I1))))) 2)))



(check-sat)
(exit)
