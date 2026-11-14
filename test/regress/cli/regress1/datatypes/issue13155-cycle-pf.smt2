; COMMAND-LINE: --inst-max-rounds=9 --check-proofs
; EXPECT: unknown
(set-logic ALL)
(declare-datatypes ((F 0)) (((L) (N (f! F)) (A (l F) (r F)) (I (h F) (rh F)) (O (lh F) (hs F)))))
(declare-fun is (F) Bool)
(declare-fun e () F)
(declare-fun s (F) F)
(assert (forall ((f F)) (= (is f) (ite ((_ is A) f) (and (is (l f))) (ite ((_ is O) f) (and (is (hs f)) (is (lh f))) true)))))
(assert (forall ((f F)) (= (s f) (ite ((_ is A) f) (A (s (l L)) (s (r f))) (ite ((_ is O) f) (O (s (lh f)) (s (hs f))) (ite ((_ is I) f) (O (N (s (h f))) (rh L)) (N (s (f! f)))))))))
(assert (exists ((B F)) (not (is (s e)))))
(check-sat)
