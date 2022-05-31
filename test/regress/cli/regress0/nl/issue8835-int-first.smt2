; EXPECT: sat
; REQUIRES: poly
(set-logic ALL)
(set-option :nl-cov true)
(declare-const x2 Int)
(declare-const x22 Int)
(declare-const x224 Int)
(declare-fun x () Int)
(assert (and (forall ((t Int)) (or (distinct 0 (+ x224 (* t x))) (and (distinct 0 (+ x22 x224 x2)) (= t 0))))))
(check-sat)
