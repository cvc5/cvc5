; COMMAND-LINE: --solve-bv-as-int=iand
; EXPECT: sat
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 1))
(declare-fun m () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (_ bv1 1) (ite (= (bvshl ((_ zero_extend 24) (select m (_ bv0 32))) (_ bv2 32)) ((_ zero_extend 24) (select (store m (_ bv0 32) ((_ zero_extend 7) x)) (_ bv0 32)))) (_ bv0 1) (_ bv1 1))))
(check-sat)
