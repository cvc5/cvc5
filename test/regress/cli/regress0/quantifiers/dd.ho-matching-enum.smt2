; COMMAND-LINE: --ieval=use
; EXPECT: unsat
(set-logic HO_ALL)
(declare-fun q (Int) Bool)
(declare-fun k (Int Int) Int)
(assert (not (q (k 0 0))))
(assert (forall ((f (-> Int Int Int))) (q (f 0 0))))
(check-sat)
