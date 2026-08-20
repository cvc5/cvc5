; COMMAND-LINE: --bv-abstraction
; EXPECT: unsat
; DISABLE-TESTER: proof
; Ported from Bitwuzla test/regress/solver/abstract/murxla-cc7db96bcf2e620d.min.smt2
; Bitwuzla's non-standard binary (bvrol (_ bv1 62) ((_ zero_extend 61) x)) rotates
; by a variable amount; for the 1-bit x here this is exactly
; (ite (= x #b1) (_ bv2 62) (_ bv1 62)).
(set-logic QF_BV)
(set-info :status unsat)
(declare-const x (_ BitVec 1))
(check-sat-assuming ((bvsaddo (_ bv0 62) (ite (= x #b1) (_ bv2 62) (_ bv1 62)))))
