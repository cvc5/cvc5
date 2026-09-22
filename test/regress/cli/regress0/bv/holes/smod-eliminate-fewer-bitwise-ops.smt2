; EXPECT: unsat
(set-logic  QF_BV)

(set-info :status unsat)

(define-fun bvsmod_def ((s (_ BitVec 13)) (t (_ BitVec 13))) (_ BitVec 13)
     (let ((sLt0 (bvuge s #b1000000000000))
           (tLt0 (bvuge t #b1000000000000))
          )
       (let ((abs_s (ite sLt0 (bvneg s) s))
             (abs_t (ite tLt0 (bvneg t) t)))
         (let ((u (bvurem abs_s abs_t)))
           (ite (= u (_ bv0 13))
                u
           (ite (and (not sLt0) (not tLt0) )
                u
           (ite (and sLt0 (not tLt0))
                (bvadd (bvneg u) t)
           (ite (and (not sLt0) tLt0)
                (bvadd u t)
                (bvneg u)))))))))

(define-fun a () (_ BitVec 13) (_ bv30 13))
(define-fun b () (_ BitVec 13) (_ bv8190 13))

(assert (not (= (bvsmod_def a b) (bvsmod a b))))

(check-sat)

(exit)
