; EXPECT: sat
; A second instance of the unsound MultSltMult rewrite from issue #13039: here
; (concat #b00 (bvadd x t) y1) is not a zero extend of (bvadd x t), so the
; rewrite must not treat it as one.
(set-logic QF_BV)
(declare-const x (_ BitVec 1))
(declare-const t (_ BitVec 1))
(declare-const y1 (_ BitVec 1))
(declare-const y2 (_ BitVec 1))
(declare-const a (_ BitVec 2))
(assert (and (= t #b0) (= x #b0) (= y1 #b0) (= y2 #b1) (= a #b01)
  (bvslt (bvmul ((_ zero_extend 2) (concat (bvadd x t) y1)) ((_ sign_extend 2) a))
         (bvmul ((_ zero_extend 2) (concat x y2)) ((_ sign_extend 2) a)))))
(check-sat)
