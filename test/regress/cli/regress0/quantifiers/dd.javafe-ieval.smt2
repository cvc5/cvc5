; COMMAND-LINE: --ieval=use
; EXPECT: unsat
(set-logic ALL)
(declare-fun m () Int)
(declare-fun s (Int Int) Int)
(declare-fun t () Int)
(declare-fun S () Int)
(declare-fun i (Int Int) Int)
(declare-fun n (Int Int) Int)
(declare-fun T () Int)
(assert (forall ((? Int)) (= (> m ?) (= S (n ? m)))))
(assert (let ((?v_15 (n m (s m m)))) (and (= S (i t T)) (= m (s m m)) (forall ((? Int)) (or (= ? (s 0 0)) (distinct S (i ? T)))) (or (= S (n m (s m m))) (exists ((? Int)) (and (distinct ? t) (= S (i ? T))))))))
(check-sat)
