; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun t () (_ BitVec 16))
(assert (not (and (<= 0 (bv2nat t)) (< (bv2nat t) 65536))))
(check-sat)
