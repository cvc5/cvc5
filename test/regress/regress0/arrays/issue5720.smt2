; COMMAND-LINE: -i
; EXPECT: unsat
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALIA)
(set-option :check-unsat-cores true)
(set-option :fmf-fun true)
(declare-fun arr0 () (Array Bool Int))
(declare-fun arr1 () (Array Int (Array Bool Int)))
(assert (xor true (= arr1 (store arr1 0 arr0))))
(push)
(assert false)
(check-sat)
(pop)
(check-sat)
