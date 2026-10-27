; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_UFBVLIA)
(set-info :status unsat)

(declare-fun x () (_ BitVec 25))
(assert (not (= (bvand x (bvshl x ((_ int_to_bv 25) 26))) (bvxor x x))))
(check-sat)
(exit)
