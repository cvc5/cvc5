; COMMAND-LINE: --uf-lazy-ll -q
; EXPECT: sat
(set-logic HO_ALL)
(declare-sort u 0)
(declare-sort m 0)
(declare-fun f ((-> m u Bool) u) Bool)
(assert (= f (lambda ((Phi (-> m u Bool)) (W u)) (forall ((X m)) (Phi X W)))))
(declare-fun m ((-> u u Bool) (-> u Bool) u) Bool)
(declare-fun m ((-> u Bool)) Bool)
(declare-fun a (u u) Bool)
(declare-fun v (m m u) Bool)
(assert (m (f (lambda ((X m) (w u)) (f (lambda ((Y m) (w u)) (m a (v X Y) w)) w)))))
(check-sat)
