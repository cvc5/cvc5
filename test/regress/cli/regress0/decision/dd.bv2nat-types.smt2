; COMMAND-LINE: --preregister-mode=rlv
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-const x (_ BitVec 1))
(assert (= (_ bv1 32) ((_ int2bv 32) (bv2nat ((_ zero_extend 7) x)))))
(check-sat)
