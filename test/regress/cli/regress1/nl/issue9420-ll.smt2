; COMMAND-LINE: --learned-rewrite
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic AUFBVFPDTNIRA)

(declare-const x Int)
(declare-const y Int)

(assert (not (= y 0)))
(assert (not (= (mod x y) (mod x (abs y)))))

(check-sat)
