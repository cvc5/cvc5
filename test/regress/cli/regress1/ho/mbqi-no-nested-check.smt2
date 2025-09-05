; COMMAND-LINE: --mbqi --no-mbqi-nested-check
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort u 0)
(declare-fun a () u)
(declare-fun f (u) u)
(declare-fun b () u)
(declare-fun p (u u) Bool)
(assert (not (=> (p a b) (=> (forall ((X u) (Y u)) (=> (p X b) (not (= X (f Y))))) (exists ((A (-> u Bool))) (and (forall ((Z u)) (not (A (f Z)))) (A a)))))))
(set-info :filename NUM802^5)
(check-sat-assuming ( true ))
