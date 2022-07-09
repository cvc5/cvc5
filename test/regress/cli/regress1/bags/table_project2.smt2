(set-logic HO_ALL)
(set-info :status sat)
(set-option :fmf-bound true)
(set-option :uf-lazy-ll true)

(declare-fun A () (Table String String))
(declare-fun B () (Table String String))

(assert (= B ((_ table.project 1 0) A)))
(assert (bag.member (tuple "y" "x") B))
(check-sat)
