; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --finite-model-find --fmf-fun --macros-quant --check-unsat-cores
; DISABLE-TESTER: model
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(declare-datatype N ((zero) (succ (pred N))))
(declare-fun evenAlias (N) Bool)
(declare-fun oddAlias (N) Bool)
(define-funs-rec ((evenRec ((x N)) Bool) (oddRec ((x N)) Bool))
 ((ite ((_ is zero) x) true (oddAlias (pred x)))
  (ite ((_ is zero) x) false (evenAlias (pred x)))))
(assert (forall ((x N)) (= (evenRec x) (evenAlias x))))
(assert (forall ((x N)) (= (oddAlias x) (oddRec x))))
(assert (evenAlias (succ (succ zero))))
(check-sat)
(assert (oddAlias (succ (succ zero))))
(check-sat)
