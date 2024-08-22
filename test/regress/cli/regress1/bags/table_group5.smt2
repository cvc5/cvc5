; DISABLE-TESTER: lfsc
; Disabled since table.group is not supported in LFSC
(set-logic HO_ALL)

(set-info :status unsat)

(declare-fun data () (Table String String String))
(declare-fun groupBy01 () (Bag (Table String String String)))
(declare-fun groupBy10 () (Bag (Table String String String)))

(assert (= groupBy01 ((_ table.group 0 1) data)))
(assert (= groupBy10 ((_ table.group 1 0) data)))
(assert (distinct groupBy01 groupBy10))

(check-sat)
