; COMMAND-LINE: --check-proofs
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-datatypes ((F 0)) (((V) (N (f F)) (A (l F)) (O (h F) (rh F)))))
(declare-fun r () F)
(declare-fun n (F) F)
(declare-fun is (F) Bool)
(assert (forall ((f F)) (= (N f) (ite ((_ is A) r) V (ite ((_ is O) r) (O V (n (rh f))) (ite x (N (rh (N r))) (ite (or ((_ is V) f) ((_ is O) r)) (l V) (ite ((_ is A) r) f r))))))))
(assert (forall ((f F)) (= ((_ is N) r) (ite ((_ is N) r) (or (is (n f))) false))))
(assert (exists ((B F)) (= (is V) (not (is (n B))))))
(check-sat)
