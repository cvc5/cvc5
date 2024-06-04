; COMMAND-LINE: --mbqi --mbqi-fast-sygus
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
;; HO not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic HO_ALL)
(declare-fun g (Int Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (forall ((h (-> Int Int Int))) (not (= (h x y) (g y x)))))
(check-sat)
