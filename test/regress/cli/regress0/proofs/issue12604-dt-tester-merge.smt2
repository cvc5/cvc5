; COMMAND-LINE: --check-proofs
; EXPECT: unknown
(set-logic ALL)
(declare-const x Bool)
(declare-datatypes ((F 0)) (((N) (A) (O (l F) (l2 F)) (a (d (_ BitVec 1)))))))
(declare-fun r () F)
(declare-fun e (F) Bool)
(declare-fun n (F) F)
(assert (forall ((o F)) (= ((_ is O) o) (ite ((_ is A) o) (or (e (n o))) (ite ((_ is N) r) false (ite false ((_ is A) N) true))))))
(assert (forall ((o F)) (= (n o) (ite ((_ is A) o) A (ite ((_ is a) r) r (O N (n r)))))))
(assert (exists ((f F)) (and (or ((_ is a) f) x) (distinct (e r) (e (n f))))))
(check-sat)
