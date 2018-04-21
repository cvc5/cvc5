; COMMAND-LINE: --bitblast=eager --no-check-proofs
; EXPECT: unsat
(set-logic QF_BV)
(set-info :status unsat)
(define-fun hamming-weight ((bv (_ BitVec 4))) (_ BitVec 4)
 (bvadd
  (bvadd
   (bvadd ((_ zero_extend 3) ((_ extract 0 0) bv))
    ((_ zero_extend 3) ((_ extract 1 1) bv)))
   ((_ zero_extend 3) ((_ extract 2 2) bv)))
  ((_ zero_extend 3) ((_ extract 3 3) bv))))
(define-fun left-hamming-weight ((index (_ BitVec 4)) (bv (_ BitVec 4)))
 (_ BitVec 4)
 (hamming-weight (bvand bv (bvnot (bvsub (bvshl index (_ bv1 4)) (_ bv1 4))))))
(define-fun right-hamming-weight ((index (_ BitVec 4)) (bv (_ BitVec 4)))
 (_ BitVec 4) (hamming-weight (bvand bv (bvsub index (_ bv1 4)))))
(define-fun bit-1 ((bv (_ BitVec 4))) (_ BitVec 4) (bvand bv (bvneg bv)))
(define-fun bit-2 ((bv (_ BitVec 4))) (_ BitVec 4)
 (bit-1 (bvand bv (bvsub bv (_ bv1 4)))))
(define-fun bit-3 ((bv (_ BitVec 4))) (_ BitVec 4)
 (bit-2 (bvand bv (bvsub bv (_ bv1 4)))))
(define-fun bit-4 ((bv (_ BitVec 4))) (_ BitVec 4)
 (bit-3 (bvand bv (bvsub bv (_ bv1 4)))))
(define-fun bit-5 ((bv (_ BitVec 4))) (_ BitVec 4)
 (bit-4 (bvand bv (bvsub bv (_ bv1 4)))))
(define-fun index-bit ((index (_ BitVec 4)) (bv (_ BitVec 4))) (_ BitVec 4)
 (ite (= index (_ bv0 4)) (bit-1 bv)
  (ite (= index (_ bv1 4)) (bit-2 bv)
   (ite (= index (_ bv2 4)) (bit-3 bv) (bit-4 bv)))))
(define-fun permute
 ((index (_ BitVec 4)) (obj-0 (_ BitVec 4)) (obj-1 (_ BitVec 4))
  (obj-2 (_ BitVec 4)) (obj-3 (_ BitVec 4)))
 (_ BitVec 4)
 (let ((my-index-bit (bvshl (_ bv1 4) index)))
  (ite (= my-index-bit obj-0) (_ bv0 4)
   (ite (= my-index-bit obj-1) (_ bv1 4)
    (ite (= my-index-bit obj-2) (_ bv2 4) (_ bv3 4))))))
(define-fun left-zeros ((index (_ BitVec 4))) (_ BitVec 8)
 (ite (bvugt index (_ bv2 4)) (ite (bvugt index (_ bv4 4)) (_ bv0 8) (_ bv1 8))
  (ite (bvugt index (_ bv1 4)) (_ bv2 8) (_ bv3 8))))
(define-fun centered ((index (_ BitVec 4)) (bv (_ BitVec 4))) (_ BitVec 8)
 (bvshl ((_ zero_extend 4) bv) (left-zeros index)))
(declare-const v0 (_ BitVec 4))
(assert (= (_ bv4 4) (hamming-weight v0)))
(declare-const v1 (_ BitVec 4))
(assert (= (_ bv4 4) (hamming-weight v1)))
(declare-const vp1-0 (_ BitVec 4))
(assert
 (or (= (_ bv1 4) vp1-0) (= (_ bv2 4) vp1-0) (= (_ bv4 4) vp1-0)
  (= (_ bv8 4) vp1-0)))
(declare-const vp1-1 (_ BitVec 4))
(assert
 (or (= (_ bv1 4) vp1-1) (= (_ bv2 4) vp1-1) (= (_ bv4 4) vp1-1)
  (= (_ bv8 4) vp1-1)))
(declare-const vp1-2 (_ BitVec 4))
(assert
 (or (= (_ bv1 4) vp1-2) (= (_ bv2 4) vp1-2) (= (_ bv4 4) vp1-2)
  (= (_ bv8 4) vp1-2)))
(declare-const vp1-3 (_ BitVec 4))
(assert
 (or (= (_ bv1 4) vp1-3) (= (_ bv2 4) vp1-3) (= (_ bv4 4) vp1-3)
  (= (_ bv8 4) vp1-3)))
(assert (= (_ bv15 4) (bvor vp1-0 (bvor vp1-1 (bvor vp1-2 vp1-3)))))
(assert
 (and
  (= (_ bv0 8)
     (bvxor
      (bvand
       (centered (index-bit (permute (_ bv0 4) vp1-0 vp1-1 vp1-2 vp1-3) v1) v1)
       (centered (index-bit (_ bv0 4) v0) v0))
      (_ bv8 8)))
  (= (_ bv0 8)
     (bvxor
      (bvand
       (centered (index-bit (permute (_ bv1 4) vp1-0 vp1-1 vp1-2 vp1-3) v1) v1)
       (centered (index-bit (_ bv1 4) v0) v0))
      (_ bv8 8)))
  (= (_ bv0 8)
     (bvxor
      (bvand
       (centered (index-bit (permute (_ bv2 4) vp1-0 vp1-1 vp1-2 vp1-3) v1) v1)
       (centered (index-bit (_ bv2 4) v0) v0))
      (_ bv8 8)))
  (= (_ bv0 8)
     (bvxor
      (bvand
       (centered (index-bit (permute (_ bv3 4) vp1-0 vp1-1 vp1-2 vp1-3) v1) v1)
       (centered (index-bit (_ bv3 4) v0) v0))
      (_ bv8 8)))))
(check-sat)

