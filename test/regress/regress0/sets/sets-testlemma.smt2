; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_UFLIA_SETS)
(set-info :status sat)
(declare-fun x () (Set (_ BitVec 2)))
(declare-fun y () (Set (_ BitVec 2)))
(assert (not (= x y)))
(check-sat)
