; COMMAND-LINE: --produce-learned-literals
; EXPECT: sat
(set-logic QF_ABV)
(declare-fun m () (_ BitVec 6))
(assert (not (bvsle (_ bv1 32) ((_ zero_extend 26) (bvsmod (_ bv0 6) (bvadd m (bvsmod (_ bv0 6) m)))))))
(assert (bvsge (_ bv63 6) m))
(check-sat)
