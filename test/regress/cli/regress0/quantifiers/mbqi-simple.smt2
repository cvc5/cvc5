; COMMAND-LINE: --mbqi
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun Q (Int) Bool)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (Q x) (P x))))
(assert (not (P 1)))
(assert (not (P 3)))
(assert (not (P 7)))
(assert (not (Q 2)))
(assert (not (Q 5)))
(check-sat)
