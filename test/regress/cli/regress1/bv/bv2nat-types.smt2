(set-logic QF_ALL)
(set-info :status sat)
(declare-fun x () (_ BitVec 8))
(assert 
(= (concat #b000000000000000000000000 x) ((_ int_to_bv 32) (ubv_to_int x)))
)
(check-sat)
