; COMMAND-LINE: --learned-rewrite
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (<= x 0) (< 0 y) (or (= 0 y) (> 0 (mod x y)))))
(check-sat)
