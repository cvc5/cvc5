; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((myType 0)) (((A) (B))))

(declare-datatypes ((|__cvc5_record_pos_(Set myType)_neg_(Set myType)| 0)) (((|__cvc5_record_pos_(Set myType)_neg_(Set myType)_ctor| (pos (Set myType)) (neg (Set myType))))))



(declare-fun emptymyTypeSet () (Set myType))
(assert (= emptymyTypeSet (as set.empty (Set myType))))
(declare-fun d () (Array myType |__cvc5_record_pos_(Set myType)_neg_(Set myType)|))
(declare-fun l () (Array myType (Set String)))
(assert (= (select l A) (set.union (set.singleton "L") (set.singleton "H"))))
(assert (= (select l B) (set.singleton "L")))
(declare-fun ic0_i () (Set myType))
(declare-fun ic0_c () (Set myType))
(assert (forall ((r myType)) (=> (set.member r ic0_i) (forall ((r2 myType)) (=> (set.member r2 (neg (select d r))) (set.member r2 ic0_c))))))
(assert (set.subset (set.singleton A) ic0_i))
(assert (or (exists ((e0 myType)) (=> (set.member e0 ic0_i) (set.subset (select l A) (select l e0)))) (set.subset (set.inter ic0_i ic0_c) emptymyTypeSet)))
(declare-fun ic1_i () (Set myType))
(declare-fun ic1_c () (Set myType))
(assert (forall ((r myType)) (=> (set.member r (pos (select d B))) (set.member r ic1_i))))
(assert (or (exists ((e1 myType)) (=> (set.member e1 ic1_i) (set.subset (select l B) (select l e1)))) (set.subset (set.inter ic1_i ic1_c) emptymyTypeSet)))
(check-sat)
