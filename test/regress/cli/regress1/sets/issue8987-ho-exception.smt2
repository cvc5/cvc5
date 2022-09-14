; EXPECT: (error "Term of kind rel.project are only supported with higher-order logic. Try adding the logic prefix HO_.")
; EXIT: 1
(set-logic ALL)
(set-option :strings-exp true)
(declare-fun e () (Relation String))
(declare-fun v () Int)
(assert (and (= (str.from_int v) (str.from_int 0)) (= (rel.project e) (rel.project (set.singleton (tuple ""))))))
(check-sat)
