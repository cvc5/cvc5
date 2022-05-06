; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: sat

(set-logic QF_BV)
(declare-fun a () (_ BitVec 1))
(assert (= (_ bv0 16) (bvsdiv ((_ zero_extend 8) ((_ zero_extend 7) a)) (bvnor (_ bv0 16) (_ bv0 16)))))
(check-sat)
