(set-logic HO_ALL)
(set-info :status sat)
(set-option :uf-lazy-ll true)

(declare-fun A () (Relation String String))
(declare-fun B () (Relation String String))

(assert (= B ((_ rel.project 1 0) A)))
(assert (set.member (tuple "y" "x") B))
(check-sat)
