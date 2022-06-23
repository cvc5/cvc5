; COMMAND-LINE: --strings-exp
; EXPECT: unknown
(set-logic ALL)
(declare-const x1 Bool)
(declare-const x Int)
(assert (forall ((e String)) (or (exists ((e String)) (or (ite (str.prefixof "-" (str.at e 0)) false (= 1 (str.to_int (str.at e (+ x (str.len e)))))) x1)))))
(check-sat)
