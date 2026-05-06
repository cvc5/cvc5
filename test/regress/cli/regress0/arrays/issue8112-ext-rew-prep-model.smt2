; COMMAND-LINE: --ext-rew-prep=agg --check-models -q
; EXPECT: sat
(set-logic QF_ABV)
(declare-fun a () (_ BitVec 1))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun d () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun e () (_ BitVec 32))
(assert
  (= (ite (distinct d
                    (store (store b
                                  ((_ zero_extend 31) a)
                                  ((_ zero_extend 7) a))
                           (_ bv0 32)
                           (_ bv0 8)))
          (_ bv1 1)
          (_ bv0 1))
     (bvxnor a
             (ite (= (_ bv1 1)
                     (ite (distinct c
                                    (store d
                                           (_ bv1 32)
                                           ((_ extract 7 0)
                                             (bvsub e (_ bv1 32)))))
                          (_ bv1 1)
                          (_ bv0 1)))
                  (_ bv1 1)
                  (_ bv0 1)))))
(check-sat)
