; COMMAND-LINE:
; EXPECT: sat
; EXPECT: ((x #b0001))
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #b0001))
(check-sat)
(get-value (x))
