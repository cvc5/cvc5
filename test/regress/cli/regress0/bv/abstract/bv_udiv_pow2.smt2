; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=16
; EXPECT: unsat
; DISABLE-TESTER: proof
; Ported from Bitwuzla test/regress/solver/abstract/bv_udiv_pow2.smt2
(set-logic QF_BV)
(set-info :status unsat)
(declare-const a (_ BitVec 16))
(declare-const b (_ BitVec 16))
(declare-const c (_ BitVec 16))
(declare-const pow2 (_ BitVec 16))
(declare-const shift_by (_ BitVec 16))
(assert (bvult shift_by (_ bv16 16)))
(assert (= pow2 (bvshl (_ bv1 16) shift_by)))
(assert (= c (bvudiv a pow2)))
(assert (distinct c (bvlshr a shift_by)))
(check-sat)
