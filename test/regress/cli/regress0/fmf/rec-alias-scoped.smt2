; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --finite-model-find --fmf-fun --macros-quant
; DISABLE-TESTER: model
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(declare-datatype N ((leaf (value Int)) (next (child N))))
(define-fun-rec validRec ((x N)) Bool
  (ite ((_ is leaf) x) (>= (value x) 0) (validRec (child x))))
(declare-fun valid (N) Bool)
(push 1)
(assert (forall ((y N)) (= (valid y) (validRec y))))
(assert (valid (next (leaf 3))))
(check-sat)
(assert (valid (leaf (- 1))))
(check-sat)
(pop 1)
(assert (valid (leaf (- 1))))
(check-sat)
