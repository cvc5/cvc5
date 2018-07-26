(set-logic QF_ALL)
(set-info :status sat)
(declare-fun x () (_ BitVec 8))
(assert 
(= (concat #b000000000000000000000000 x) ((_ int2bv 32) (bv2nat x)))
)
(check-sat)
