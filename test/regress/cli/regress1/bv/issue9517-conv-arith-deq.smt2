; EXPECT: sat
(set-logic ALL)
(set-option :produce-interpolants true)
(declare-const x Bool)
(declare-fun v () Int)
(assert (xor x (not x) (= 0 (ubv_to_int ((_ int_to_bv 3) v)))))
(check-sat)
