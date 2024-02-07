; COMMAND-LINE: --mbqi
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort $$unsorted 0)
(declare-fun tptp.in ($$unsorted $$unsorted) Bool)
(declare-fun tptp.dsetconstr ($$unsorted (-> $$unsorted Bool)) $$unsorted)
(declare-fun tptp.dsetconstrI () Bool)
(assert (= tptp.dsetconstrI (forall ((A $$unsorted) (Xphi (-> $$unsorted Bool)) (Xx $$unsorted)) (let ((_let_1 (@ tptp.in Xx))) (=> (@ _let_1 A) (=> (@ Xphi Xx) (@ _let_1 (@ (@ tptp.dsetconstr A) (lambda ((Xy $$unsorted)) (@ Xphi Xy))))))))))
(declare-fun tptp.binintersect ($$unsorted $$unsorted) $$unsorted)
(assert (= tptp.binintersect (lambda ((A $$unsorted) (B $$unsorted)) (@ (@ tptp.dsetconstr A) (lambda ((Xx $$unsorted)) (@ (@ tptp.in Xx) B))))))
(assert (not (=> tptp.dsetconstrI (forall ((A $$unsorted) (B $$unsorted) (Xx $$unsorted)) (let ((_let_1 (@ tptp.in Xx))) (=> (@ _let_1 A) (=> (@ _let_1 B) (@ _let_1 (@ (@ tptp.binintersect A) B)))))))))
(set-info :filename SEU589^2)
(check-sat-assuming ( true ))
