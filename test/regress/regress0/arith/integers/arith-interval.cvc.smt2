; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Int)
(declare-fun P (Int) Bool)
(assert (and (<= 1 x) (<= x 2)))
(assert (and (P 1) (P 2)))
(check-sat-assuming ( (not (P x)) ))
