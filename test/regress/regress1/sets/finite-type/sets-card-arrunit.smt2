(set-logic QF_ALL)
(set-info :status unsat)
(set-option :sets-ext true)
(declare-datatype Unit ((mkUnit)))

(declare-fun S () (Set (Array Int Unit)))

(assert (> (set.card S) 1))

(check-sat)
