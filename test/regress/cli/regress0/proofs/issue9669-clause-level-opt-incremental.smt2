; COMMAND-LINE: -i --check-proofs
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic QF_UFLIA)
(declare-const x1 Bool)
(declare-const x7 Bool)
(declare-const x74 Bool)
(declare-const x4 Bool)
(declare-const x2 Bool)
(declare-const x22 Bool)
(declare-const x24 Bool)
(declare-const x3 Bool)
(declare-fun x (Int) Int)
(assert (and (and true (or x1 (not x74))) (and (or x24 (= (x 3) (x 1))) (and (= 1 (x 0)) (or x22 (= (x 1) (x 0))) (or x22 (not (and x1 x24))) (or x74 (not (and x7 x22))))) (and (or x74 x7) (or (and x1 x24) (= (x 2) (+ 1 (x 3))))) (and (or x74 (= (x 4) (x 2))) (or (not x2) (= (x 4) (+ 1 (x 2))))) (or (not x3) x4)))
(check-sat)
(assert (and x7 (or x2 x4) (= 0 (* 1 (x (- 5 1))))))
(push)
(check-sat)
(check-sat)
(pop)