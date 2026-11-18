; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic ALL)
(declare-const p Bool)
(declare-const i1 Int)
(declare-const a0 (Array Real Int))
(declare-const a2 (Array Real Int))
(assert (xor p (not (= a2 (store a0 1.0 (- 2))))))
(assert (= (select a0 2.0) (select a0 (to_real (+ i1 1)))))
(check-sat)
