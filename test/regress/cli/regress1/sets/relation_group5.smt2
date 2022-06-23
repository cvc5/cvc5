; DISABLE-TESTER: lfsc
; Disabled since table.group is not supported in LFSC
(set-logic HO_ALL)

(set-info :status unsat)

(declare-fun data () (Relation String String String))
(declare-fun groupBy01 () (Set (Relation String String String)))
(declare-fun groupBy10 () (Set (Relation String String String)))

(assert (= groupBy01 ((_ rel.group 0 1) data)))
(assert (= groupBy10 ((_ rel.group 1 0) data)))
(assert (distinct groupBy01 groupBy10))

(check-sat)
