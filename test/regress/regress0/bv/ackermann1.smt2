; COMMAND-LINE: --bitblast=eager --no-check-models  --no-check-unsat-cores
; COMMAND-LINE: --bitblast=eager --bv-solver=simple --no-check-models  --no-check-unsat-cores
; EXPECT: sat
(set-logic QF_UFBV)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(declare-fun v0 () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 4))

(assert (= (f (f v0)) (g (f v0))))


(check-sat)
(exit)
