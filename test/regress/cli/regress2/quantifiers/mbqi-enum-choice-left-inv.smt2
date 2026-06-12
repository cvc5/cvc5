; COMMAND-LINE: --mbqi-enum --mbqi-enum-choice-grammar --no-mbqi-nested-check
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort u 0)
(declare-fun f (u) u)                                                                                             
(assert (forall ((X u) (Y u)) (=> (= (f X) (f Y)) (= X Y))))
(assert (forall ((G (-> u u))) (exists ((X u)) (not (= (G (f X)) X)))))
(check-sat)
(exit)
