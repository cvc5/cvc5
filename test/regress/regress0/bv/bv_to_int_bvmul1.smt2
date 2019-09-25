; COMMAND-LINE: --solve-bv-as-int=1 --no-check-models  --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int=4 --no-check-models  --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int=8 --no-check-models  --no-check-unsat-cores
; EXPECT: sat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (bvult (bvmul a b) (bvudiv a b)))

(check-sat)
