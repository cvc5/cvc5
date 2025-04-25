; COMMAND-LINE: --mbqi --mbqi-enum
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort a 0)
(declare-fun f (a) a)
(declare-fun g (a) a)
(assert (not (=> (forall ((X a) (P (-> a Bool))) (=> (P (g X)) (P (f X)))) (= g f))))
(set-info :filename SYO233^5)
(check-sat-assuming ( true ))
