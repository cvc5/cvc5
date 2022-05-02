; EXPECT: unknown
(set-logic HO_ALL)
(declare-sort $$unsorted 0)
(declare-sort mu 0)

(declare-fun mnot ((-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mnot (lambda ((Phi (-> $$unsorted Bool)) (W $$unsorted)) (not (Phi W)))))

(declare-fun mor ((-> $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mor (lambda ((Phi (-> $$unsorted Bool)) (Psi (-> $$unsorted Bool)) (W $$unsorted)) (or (Phi W) (Psi W)))))

(declare-fun mand ((-> $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mand (lambda ((Phi (-> $$unsorted Bool)) (Psi (-> $$unsorted Bool)) (__flatten_var_0 $$unsorted)) (mnot (mor (mnot Phi) (mnot Psi)) __flatten_var_0))))

(declare-fun mimplies ((-> $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mimplies (lambda ((Phi (-> $$unsorted Bool)) (Psi (-> $$unsorted Bool)) (__flatten_var_0 $$unsorted)) (mor (mnot Phi) Psi __flatten_var_0))))

(declare-fun mforall_ind ((-> mu $$unsorted Bool) $$unsorted) Bool)
(assert (= mforall_ind (lambda ((Phi (-> mu $$unsorted Bool)) (W $$unsorted)) (forall ((X mu)) (Phi X W) ))))

(declare-fun mbox ((-> $$unsorted $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mbox (lambda ((R (-> $$unsorted $$unsorted Bool)) (Phi (-> $$unsorted Bool)) (W $$unsorted)) (forall ((V $$unsorted)) (or (not (R W V)) (Phi V)) ))))

(declare-fun mvalid ((-> $$unsorted Bool)) Bool)
(assert (= mvalid (lambda ((Phi (-> $$unsorted Bool))) (forall ((W $$unsorted)) (Phi W) ))))

(declare-fun a1 ($$unsorted $$unsorted) Bool)
(declare-fun a2 ($$unsorted $$unsorted) Bool)
(declare-fun a3 ($$unsorted $$unsorted) Bool)

(declare-fun jan () mu)
(declare-fun cola () mu)

(declare-fun likes (mu mu $$unsorted) Bool)

(declare-fun very_much_likes (mu mu $$unsorted) Bool)

(assert (mvalid (mforall_ind (lambda ((X mu) (__flatten_var_0 $$unsorted)) (mforall_ind (lambda ((Y mu) (__flatten_var_0 $$unsorted)) (mbox a3 (mimplies (mand (likes X Y) (mand (mbox a1 (likes X Y)) (mbox a2 (likes X Y)))) (very_much_likes X Y)) __flatten_var_0)) __flatten_var_0)))))

(check-sat)