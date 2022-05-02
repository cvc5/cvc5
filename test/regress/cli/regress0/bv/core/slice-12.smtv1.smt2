; REQUIRES: cryptominisat
; COMMAND-LINE: --bitblast=eager --bv-sat-solver=cryptominisat
; EXPECT: unsat
(set-option :incremental false)
(set-info :status unsat)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z1 () (_ BitVec 4))
(declare-fun z2 () (_ BitVec 4))
(assert (= x (_ bv85 8)))
(assert (= y (_ bv170 8)))
(assert (= z1 (concat (concat (concat ((_ extract 0 0) x) ((_ extract 2 2) x)) ((_ extract 4 4) x)) ((_ extract 6 6) x))))
(assert (= z2 (concat (concat (concat ((_ extract 7 7) y) ((_ extract 5 5) y)) ((_ extract 3 3) y)) ((_ extract 1 1) y))))
(check-sat-assuming ( (not (= z1 z2)) ))
