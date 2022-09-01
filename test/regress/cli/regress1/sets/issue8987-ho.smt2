; COMMAND-LINE: --uf-lazy-ll
; EXPECT: sat
(set-logic HO_ALL)
(set-option :strings-exp true)
(declare-fun e () (Relation String))
(declare-fun v () Int)
(assert (and (= (str.from_int v) (str.from_int 0)) (= (rel.project e) (rel.project (set.singleton (tuple ""))))))
(check-sat)
