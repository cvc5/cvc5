; COMMAND-LINE: --uf-lazy-ll --mbqi
; EXPECT: sat
(set-logic HO_ALL)
(declare-sort u 0)
(declare-sort ms 0)
(declare-fun f ((-> ms u Bool) u) Bool)
(assert (= f (lambda ((Phi (-> ms u Bool)) (W u)) (forall ((X ms)) (Phi X W)))))
(declare-fun m ((-> u u Bool) (-> u Bool) u) Bool)
(declare-fun m ((-> u Bool)) Bool)
(declare-fun a (u u) Bool)
(declare-fun v (ms ms u) Bool)
(assert (m (f (lambda ((X ms) (w u)) (f (lambda ((Y ms) (w u)) (m a (v X Y) w)) w)))))
(check-sat)
