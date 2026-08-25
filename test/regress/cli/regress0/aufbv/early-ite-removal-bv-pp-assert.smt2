; COMMAND-LINE: --early-ite-removal
; EXPECT: unsat
(set-logic QF_ABV)
(set-info :status unsat)
(declare-fun m () (Array (_ BitVec 64) (_ BitVec 8)))
(assert
 (and
  (= (_ bv1 1)
     ((_ extract 0 0)
      (ite (= (_ bv0 32)
              (bvand (_ bv3 32)
                     (concat (_ bv0 16) (_ bv0 8) (select m (_ bv0 64)))))
           (_ bv1 32)
           (_ bv0 32))))
  (not
   (= (_ bv1 1)
      ((_ extract 0 0)
       (ite (bvult (bvand (_ bv1 32)
                          (concat (_ bv0 16)
                                  (_ bv0 8)
                                  (select m (_ bv0 64))))
                   (_ bv1 32))
            (_ bv1 32)
            (_ bv0 32)))))))
(check-sat)
