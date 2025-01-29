; EXPECT: unsat
; DISABLE-TESTER: unsat-core
(set-logic NIA)
(declare-const x Int)
(assert (or (forall ((v Int) (v_ Int)) (or (= 1 v) (< 16777215 (mod (+ v_ (mod (+ x (mod v_ 8)) 53687091)) 33554432))))))
(check-sat)
