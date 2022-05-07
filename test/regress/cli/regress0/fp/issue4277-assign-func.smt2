; EXPECT: sat
(set-logic HO_ALL)
(set-option :assign-function-values false)
(set-info :status sat)
(declare-fun b () (_ BitVec 1))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 23))
(assert (= 0.0 (fp.to_real (fp b c d))))
(check-sat)
