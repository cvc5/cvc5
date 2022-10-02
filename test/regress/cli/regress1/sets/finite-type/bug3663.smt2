;EXIT: 1
;EXPECT: (error "The cardinality beth[0] of the finite type a is not supported yet.")
(set-logic ALL)
(set-option :fmf-fun true)
(declare-sort a 0)
(declare-const b (Set a))
(assert (= (set.card b) 0))
(check-sat)
