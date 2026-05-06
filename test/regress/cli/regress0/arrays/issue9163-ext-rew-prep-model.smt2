; COMMAND-LINE: --ext-rew-prep=agg --check-models -q
; EXPECT: sat
(set-logic QF_ABV)
(declare-const x (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun e () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun t () (_ BitVec 1))
(declare-fun r () (_ BitVec 32))
(assert
  (= (_ bv1 1)
     (bvxnor t
             (bvand
               (bvcomp (_ bv0 1)
                       (ite (distinct e
                                      (store x
                                             (_ bv0 32)
                                             ((_ zero_extend 7) t)))
                            (_ bv1 1)
                            (_ bv0 1)))
               (ite (distinct (_ bv1 1)
                              (ite (distinct e
                                             (store x
                                                    (_ bv1 32)
                                                    ((_ extract 7 0)
                                                      (bvsub r (_ bv1 32)))))
                                   (_ bv1 1)
                                   (_ bv0 1)))
                    (_ bv1 1)
                    (_ bv0 1))))))
(check-sat)
