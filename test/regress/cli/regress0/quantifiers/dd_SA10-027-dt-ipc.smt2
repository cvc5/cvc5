; EXPECT: unsat
; DISABLE-TESTER: cpc
; Disabled cpc due to overloaded constructors
(set-logic ALL)
(declare-sort i 0)
(declare-sort s 0)
(declare-datatypes ((u 0)) (((us (r Bool) (e Int) (c s)))))
(declare-datatypes ((us_ 0)) (((us (c i) (e u)))))
(declare-datatypes ((_r 0)) (((s_ (_s us_)))))
(declare-fun s_ (s) _r)
(declare-fun us (_r) s)
(assert (forall ((x _r)) (= x (s_ (us x)))))
(declare-const n u)
(assert (exists ((x_ us_)) (not (=> (r n) (= (s_ x_) (s_ (c (us false 0 (us (s_ (us (c (_s (s_ (c n)))) n))))))) (forall ((o u)) (or (forall ((x us_)) (or (forall ((o u)) (or (forall ((x us_)) (or (forall ((o u)) (or (forall ((x us_)) (or (exists ((t u)) (= (r o) (= (r o) (r (e (_s (s_ (c t)))))))) (= (s_ x_) (s_ (c (us false 0 (us (s_ (us (c (_s (s_ (c o)))) (us (r (e (_s (s_ (c (us false 0 (us (s_ x_)))))))) (e (e (_s (s_ (c o))))) (us (s_ x_))))))))))))))))))))))))))
(check-sat)
