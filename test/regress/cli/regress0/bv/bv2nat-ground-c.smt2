; EXPECT: unsat
(set-logic QF_UFBVLIA)
(set-info :status unsat)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const c (_ BitVec 32))
(declare-const d (_ BitVec 32))
(declare-const e (_ BitVec 32))

(assert (or (= a #x00000007) (= a #x00000005) (= a #x00000100)))

(assert (not (= (bv2nat a) 7)))
(assert (not (= (bv2nat a) 5)))
(assert (< (bv2nat a) 10))

(check-sat)
