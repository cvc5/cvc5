; COMMAND-LINE: --proof-check=eager
; EXPECT: sat
(set-logic ALL)
(declare-fun F () Int)
(declare-fun e (Int Int) Int)
(declare-fun I (Int) Int)
(declare-fun N () Int)
(declare-fun S () Int)
(declare-fun A () Int)
(declare-fun I (Int Int) Int)
(assert (or
(exists ((? Int) (r Int)) (not (=> (and (= S (I r)) (= S (I ?)) (= S (I r A)) (= S (I ? A))) (and (distinct ? N) (distinct r N) (distinct ? r) (distinct N (e F ?)) (distinct N (e F r))) (distinct (e F ?) (e F r)))))
(forall ((? Int)) (forall ((E Int)) (forall ((r Int)) (=> (and (= S (I r)) (= S (I ?)) (= S (I r A)) (= S (I ? A))) (and (distinct ? N) (distinct r N) (distinct ? r) (distinct N (e F ?)) (distinct N (e F r))) (distinct (e F ?) (e F r))))))))
(check-sat)
