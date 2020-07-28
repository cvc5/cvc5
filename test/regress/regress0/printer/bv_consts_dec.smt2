; COMMAND-LINE: --bv-print-consts-as-indexed-symbols
; EXPECT: sat
; EXPECT: ((x (_ bv1 4)))
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #b0001))
(check-sat)
(get-value (x))
