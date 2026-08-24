; COMMAND-LINE: --bv-abstraction
; EXPECT: unsat
; DISABLE-TESTER: proof
; Ported from Bitwuzla test/regress/solver/abstract/eagerrefine1.smt2
(set-logic QF_BV)
(set-info :status unsat)
(declare-const x (_ BitVec 1))
(check-sat-assuming ((bvuaddo ((_ zero_extend 99) x) (bvsdiv (_ bv1 100) ((_ zero_extend 99) x)))))
