; COMMAND-LINE: --no-check-proofs --no-check-unsat-cores
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-fun t () (_ BitVec 16))
(assert (not (= t ((_ int2bv 16) (bv2nat t)))))
(check-sat)
