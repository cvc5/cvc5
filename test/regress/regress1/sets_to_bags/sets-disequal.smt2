; COMMAND-LINE: --incremental --no-check-proofs
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXIT: 0
(set-logic QF_BVFS)
(declare-fun S1 () (Bag (_ BitVec 1)))
(declare-fun S2 () (Bag (_ BitVec 1)))
(declare-fun S3 () (Bag (_ BitVec 1)))
(declare-fun S4 () (Bag (_ BitVec 1)))
(assert (distinct S1 S2 S3 S4))
(check-sat)
;(get-model)
(declare-fun S5 () (Bag (_ BitVec 1)))
(assert (not (= S5 S1)))
(assert (not (= S5 S2)))
(assert (not (= S5 S3)))
(check-sat)
(assert (not (= S5 S4)))
(check-sat)
