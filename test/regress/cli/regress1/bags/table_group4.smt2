(set-logic HO_ALL)

(set-info :status sat)

(declare-fun data () (Table String String String))
(declare-fun groupBy0 () (Bag (Table String String String)))
(declare-fun groupBy1 () (Bag (Table String String String)))

(assert (= groupBy0 ((_ table.group 0) data)))
(assert (= groupBy1 ((_ table.group 1) data)))
(assert (distinct groupBy0 groupBy1))

(check-sat)
