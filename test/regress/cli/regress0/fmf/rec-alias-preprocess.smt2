; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --finite-model-find --fmf-fun --macros-quant
; DISABLE-TESTER: model
; EXPECT: sat
; EXPECT: ((witness (leaf 0)) ((valid witness) true) ((validRec witness) true))
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(set-option :produce-models true)
(declare-datatype N ((leaf (value Int)) (next (child N))))
(declare-fun valid (N) Bool)
(define-fun-rec validRec ((x N)) Bool
  (ite ((_ is leaf) x) (>= (value x) 0) (validRec (child x))))
(assert (forall ((x N)) (! (= (validRec x) (valid x)) :pattern ((valid x)))))
(declare-const witness N)
(assert (= witness (leaf 0)))
(assert (valid witness))
(check-sat)
(get-value (witness (valid witness) (validRec witness)))
(push 1)
(assert (not (validRec witness)))
(check-sat)
(pop 1)
(check-sat)
