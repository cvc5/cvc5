; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((myType 0)) (((A) (B))))

(declare-datatypes ((|__cvc5_record_pos_(Set myType)_neg_(Set myType)| 0)) (((|__cvc5_record_pos_(Set myType)_neg_(Set myType)_ctor| (pos (Set myType)) (neg (Set myType))))))



(declare-fun emptymyTypeSet () (Set myType))
(assert (= emptymyTypeSet (as emptyset (Set myType))))
(declare-fun d () (Array myType |__cvc5_record_pos_(Set myType)_neg_(Set myType)|))
(declare-fun l () (Array myType (Set String)))
(assert (= (select l A) (union (singleton "L") (singleton "H"))))
(assert (= (select l B) (singleton "L")))
(declare-fun ic0_i () (Set myType))
(declare-fun ic0_c () (Set myType))
(assert (forall ((r myType)) (=> (member r ic0_i) (forall ((r2 myType)) (=> (member r2 (neg (select d r))) (member r2 ic0_c))))))
(assert (subset (singleton A) ic0_i))
(assert (or (exists ((e0 myType)) (=> (member e0 ic0_i) (subset (select l A) (select l e0)))) (subset (intersection ic0_i ic0_c) emptymyTypeSet)))
(declare-fun ic1_i () (Set myType))
(declare-fun ic1_c () (Set myType))
(assert (forall ((r myType)) (=> (member r (pos (select d B))) (member r ic1_i))))
(assert (or (exists ((e1 myType)) (=> (member e1 ic1_i) (subset (select l B) (select l e1)))) (subset (intersection ic1_i ic1_c) emptymyTypeSet)))
(check-sat)
