; COMMAND-LINE: --no-bv-print-consts-in-binary
; EXPECT: sat
; EXPECT: ((x (_ bv1 4)))
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #b0001))
(check-sat)
(get-value (x))
