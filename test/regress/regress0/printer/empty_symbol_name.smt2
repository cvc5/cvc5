; EXPECT: sat
; EXPECT: ((|| (_ bv1 4)))
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const || (_ BitVec 4))
(assert (= || #b0001))
(check-sat)
(get-value (||))
