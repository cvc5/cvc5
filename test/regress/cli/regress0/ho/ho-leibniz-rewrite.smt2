; COMMAND-LINE: --mbqi --leibniz-elim
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort a 0)
(declare-fun j (a) a)
(declare-fun g ((-> a a) a) a)
(declare-fun h (a) a)
(declare-fun f ((-> a a) a) a)
(assert (forall ((Y a) (Q (-> a Bool)) (X (-> a a))) (=> (Q (f X Y)) (Q (g X Y)))))
(assert (forall ((Z a) (Q (-> a Bool))) (=> (Q (h Z)) (Q (j Z)))))
(assert (exists ((Q1 (-> (-> a a) Bool))) (not (=> (Q1 (f h)) (Q1 (g j))))))
(check-sat)