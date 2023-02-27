; EXPECT: sat
(set-logic ALL)
(set-option :produce-interpolants true)
(declare-const x Bool)
(declare-fun v () Int)
(assert (xor x (not x) (= 0 (bv2nat ((_ int2bv 3) v)))))
(check-sat)
