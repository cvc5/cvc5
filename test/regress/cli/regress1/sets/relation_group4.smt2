(set-logic HO_ALL)

(set-info :status sat)

(declare-fun data () (Relation String String String))
(declare-fun groupBy0 () (Set (Relation String String String)))
(declare-fun groupBy1 () (Set (Relation String String String)))

(assert (= groupBy0 ((_ rel.group 0) data)))
(assert (= groupBy1 ((_ rel.group 1) data)))
(assert (distinct groupBy0 groupBy1))

(check-sat)
