; COMMAND-LINE: --incremental --check-proofs --proof-check=eager
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(assert (or (> (+ x2 (* 5 x)) 12) (= x2 0)))
(assert (or (= x 1) (< (+ (* 7 x1) (* x2 (- x))) 0)))
(assert (> (+ (* x1 x1) (* x (- 1))) 10))
(assert (< x 0))
(check-sat)
(push)
(check-sat)
(pop)
(assert (= x1 0))
(check-sat)
