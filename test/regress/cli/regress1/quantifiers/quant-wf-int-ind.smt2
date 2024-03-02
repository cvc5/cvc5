; COMMAND-LINE: --int-wf-ind
; EXPECT: unsat
;; introduces fresh Skolem in a trusted step
; DISABLE-TESTER: alethe
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (P x) (P (+ x 1)))))
(declare-fun k () Int)
(assert (P k))
(assert (exists ((y Int)) (and (>= y 0) (not (P (+ y k))))))
; requires well-found induction on integers
(check-sat)
