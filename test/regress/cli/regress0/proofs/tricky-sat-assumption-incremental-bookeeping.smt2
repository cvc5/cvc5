; COMMAND-LINE: -i --produce-proofs --proof-check=eager
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_UFLIA)
(declare-fun x (Int) Bool)
(declare-fun y (Int) Bool)
(declare-fun z (Int) Int)
(declare-fun _z (Int) Int)
(assert (= (x 0) (not (y 0))))
(assert (= (y 0) (> 0 (z 0))))
(assert (= (z 0) (_z 0)))
(assert (= 0 (_z 0)))
(push)
(check-sat)
(pop)
(assert (not (x 0)))
(check-sat)
