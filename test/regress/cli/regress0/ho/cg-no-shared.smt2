; COMMAND-LINE: --mbqi
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort a 0)
(declare-fun j (a) a)
(declare-fun h (a) a)
(declare-fun f ((-> a a)) a)
(assert (forall ((Z a)) (= (h Z) (j Z))))
(assert (not (= (f h) (f j))))
(check-sat)
