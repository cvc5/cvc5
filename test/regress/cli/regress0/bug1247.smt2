; COMMAND-LINE: --incremental
; EXPECT: unsat
;; define-const is not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_ABV)
(set-info :status unsat)

(declare-const p Bool)
(declare-const u (_ BitVec 8))
(declare-const v (_ BitVec 8))
(define-const t (_ BitVec 8) (ite p u v))
(assert (= t #x01))

(push)
(assert (= t #x00))
(check-sat)
