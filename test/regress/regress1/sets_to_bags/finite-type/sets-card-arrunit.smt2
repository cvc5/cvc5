(set-logic QF_ALL)
(set-info :status unsat)
(set-option :sets-ext true)
(declare-datatype Unit ((mkUnit)))

(declare-fun S () (Bag (Array Int Unit)))

(assert (> (bag.card S) 1))

(check-sat)
