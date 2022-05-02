; COMMAND-LINE: --bitblast=eager 
; REQUIRES: cryptominisat
; COMMAND-LINE: --bitblast=eager --bv-sat-solver=cryptominisat
; EXPECT: unsat
(set-logic QF_UFBV)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun v0 () (_ BitVec 4))
(declare-fun v1 () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 4))
(declare-fun h ((_ BitVec 4)) (_ BitVec 4))

(assert (not (= (f (g (h v0))) (f (g (h v1))))))
(assert (= v0 v1))


(check-sat)
(exit)
