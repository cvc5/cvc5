; COMMAND-LINE: --incremental --fmf-fun --macros-quant --macros-quant-mode=ground
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
; unknowns when testing unsat cores
(set-logic UFLIA)

(define-fun f ((x Int)) Int x)

(define-fun-rec g ((x Int)) Int (ite (<= x 0) 0 (+ (g x) x)))

(declare-fun h (Int) Int)
(assert (forall ((x Int)) (= (h x) (+ x 3))))

; EXPECT: sat
(check-sat)

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

; EXPECT: unsat
(push 1)
(assert (= (h 1) 5))
(check-sat)
(pop 1)
