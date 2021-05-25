; COMMAND-LINE: --bitblast=eager --no-check-models 
; COMMAND-LINE: --bitblast=eager --bv-solver=simple --no-check-models 
; EXPECT: sat
(set-logic QF_UFBV)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(declare-fun v0 () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 4))

(assert (= (f (f v0)) (g (f v0))))


(check-sat)
(exit)
