; COMMAND-LINE: --no-check-proofs --no-check-unsat-cores
; EXPECT: unsat
(set-logic QF_BVLIA)
(set-info :status unsat)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const c (_ BitVec 32))
(declare-const d (_ BitVec 32))
(declare-const e (_ BitVec 32))

(assert (or (= a b) (= a c) (= a d) (= a e)))

(assert (not (= (bv2nat a) (bv2nat b))))
(assert (not (= (bv2nat a) (bv2nat c))))
(assert (not (= (bv2nat a) (bv2nat d))))
(assert (not (= (bv2nat a) (bv2nat e))))

(check-sat)
