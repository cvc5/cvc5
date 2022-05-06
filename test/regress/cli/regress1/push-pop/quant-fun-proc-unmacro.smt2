; COMMAND-LINE: --incremental --fmf-fun --macros-quant
; DISABLE-TESTER: model
(set-logic UFLIA)


(define-fun f ((x Int)) Int x)

(define-fun-rec g ((x Int)) Int (ite (<= x 0) 0 (+ (g x) x)))

; EXPECT: sat
(declare-fun h (Int) Int)
(push 1)
(assert (forall ((x Int)) (= (h x) 0)))
(check-sat)
(pop 1)


; EXPECT: unsat
(push 1)
(assert (= (f 1) 2))
(check-sat)
(pop 1)

; EXPECT: unsat
(push 1)
(assert (= (g 1) 5))
(check-sat)
(pop 1)

; EXPECT: sat
(push 1)
(assert (= (h 1) 5))
(check-sat)
(pop 1)

