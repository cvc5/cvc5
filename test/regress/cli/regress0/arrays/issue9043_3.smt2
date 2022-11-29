; EXPECT: sat
; EXPECT: sat
(set-logic QF_ABV)
(set-info :status sat)
(set-option :incremental true)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (_ bv1 32) ((_ zero_extend 24) (select a (_ bv0 32)))))
(assert (not (= (_ bv0 32) ((_ zero_extend 24) (select a (bvadd (_ bv0 32) ((_ zero_extend 24) (select a (_ bv1 32)))))))))
(assert (not (= (_ bv0 32) ((_ zero_extend 24) (select a ((_ zero_extend 24) (select a (bvadd (_ bv3 32) ((_ zero_extend 24) (select a (_ bv1 32)))))))))))
(check-sat)
(assert (bvsle (_ bv0 32) (bvadd (_ bv1 32) ((_ zero_extend 24) (select a (_ bv0 32))) (bvnor (_ bv0 32) ((_ zero_extend 24) (select a (bvshl (_ bv3 32) ((_ zero_extend 24) (select a (_ bv1 32))))))))))
(check-sat)
