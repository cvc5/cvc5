; COMMAND-LINE: -q --check-models
(set-logic QF_UFBVLIA)
(set-info :status sat)
(declare-fun f ((_ BitVec 3)) Int)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 3))
(assert (not (= (f (bvxor x y)) (f (bvxnor x y)))))
(check-sat)
