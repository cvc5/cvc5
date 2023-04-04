; EXPECT: sat
; EXPECT: (
; EXPECT: )
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(set-option :proof-prune-input true)
(set-option :dump-difficulty true)
(assert (distinct (_ bv0 98) ((_ sign_extend 77) (bvsdiv (_ bv0 21) (bvlshr (_ bv1 21) ((_ zero_extend 20) __))))))
(check-sat)
