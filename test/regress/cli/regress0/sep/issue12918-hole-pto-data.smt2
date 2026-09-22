; REQUIRES: unrestricted-mode
; COMMAND-LINE: --produce-models
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(set-option :default-function-value-mode hole)
(declare-heap ((_ BitVec 36) (_ BitVec 36)))
(declare-fun f ((_ BitVec 36)) (_ BitVec 36))
(declare-const a (_ BitVec 36))
(assert (sep (pto a (f a)) (bvslt a #xbeae7625a)))
(check-sat)
