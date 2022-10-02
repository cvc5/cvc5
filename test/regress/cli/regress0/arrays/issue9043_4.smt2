; EXPECT: sat
; EXPECT: sat
(set-logic QF_ABV)
(set-info :status sat)
(set-option :incremental true)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (_ bv1 32) ((_ zero_extend 24) (select a (_ bv242 32)))))
(assert (not (= (_ bv0 32) ((_ zero_extend 24) (select a (bvadd (_ bv242 32) ((_ zero_extend 24) (select a (_ bv0 32)))))))))
(check-sat)
(assert (not (bvsle #b00000000000000000000000000000100 (bvadd  (_ bv1 32) ((_ zero_extend 24) (select a (bvadd ((_ zero_extend 24) (select a (_ bv0 32))) (_ bv243 32))))))))
(assert (not (= (_ bv0 32) ((_ zero_extend 24) (select a (bvadd (_ bv0 32) ((_ zero_extend 24) (select a (bvsmod (_ bv243 32) ((_ zero_extend 24) (select a (_ bv0 32))))))))))))
(check-sat)
