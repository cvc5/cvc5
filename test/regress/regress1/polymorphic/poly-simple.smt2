; COMMAND-LINE: --quant-polymorphic
; EXPECT: unsat
(set-logic UFLIA)
(declare-fun f (par (a) (a) a))

(declare-fun c (par (a) () a))

(assert (par (a) (= (f (as c a)) (as c a))))

(declare-fun P (par (a) (a) Bool))
(assert (par (a) (forall ((x a)) (= (P x) (= (f (as x a)) (as c a))))))

(declare-fun b (par (a) () a))

(assert (not (P (as c Int))))

; does not work (no base types)
;(assert (par (a) (not (P (as c a)))))
;(declare-fun Q (Real) Bool)
;(assert (Q (as c Real)))

(check-sat)
