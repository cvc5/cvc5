; EXPECT: unsat
;; unsupported operator int.pow2
; DISABLE-TESTER: alethe
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)

(assert (and (<= 0 x) (< x 16)))
(assert (< (int.pow2 x) x))

(check-sat)
