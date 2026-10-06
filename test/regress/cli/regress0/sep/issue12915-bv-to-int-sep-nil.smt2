; REQUIRES: unrestricted-mode
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(set-option :solve-bv-as-int bitwise)
(declare-heap ((_ BitVec 4) (_ BitVec 4)))
(assert (= (as sep.nil (_ BitVec 4)) (_ bv0 4)))
(check-sat)
