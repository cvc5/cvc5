; COMMAND-LINE: --cegqi-inf-int -q
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Real)
(assert
  (forall ((v Int) (r Int))
    (distinct true (>= r (* v (- 1 a) (/ 1 2))))))
(check-sat)
