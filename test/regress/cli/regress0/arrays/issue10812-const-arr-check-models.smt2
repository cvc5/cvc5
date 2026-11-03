; REQUIRES: unrestricted-mode
; COMMAND-LINE: --arrays-exp
; EXPECT: sat
(set-option :produce-models true)
(set-option :check-models true)
(set-logic QF_ABVNIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (select (ite (or (bvsaddo (ite true (_ bv12080 15) (_ bv4994 15)) ((_ zero_extend 2) (_ bv7685 13))) (bvsge ((_ rotate_left 14) (_ bv31157 15)) (bvshl (_ bv40 15) (_ bv1838 15)))) (store (ite (ite true true true) ((as const (Array Int Bool)) true) (ite true ((as const (Array Int Bool)) false) ((as const (Array Int Bool)) true))) ((_ iand 3) (* a a) (abs a)) (bvuge (bvneg (_ bv571 10)) (ite false (_ bv886 10) (_ bv735 10)))) ((as const (Array Int Bool)) false)) (ite (bvuge (bvshl (bvor (_ bv281634 19) (_ bv475899 19)) (select ((as const (Array (_ BitVec 22) (_ BitVec 19))) (_ bv358718 19)) (_ bv3478601 22))) (bvxor (select ((as const (Array Bool (_ BitVec 19))) (_ bv346106 19)) true) (select ((as const (Array (_ BitVec 21) (_ BitVec 19))) (_ bv177305 19)) (_ bv1018288 21)))) (+ (* (mod a a) (mod a a)) (abs (int.pow2 a))) (+ (select (ite true ((as const (Array Int Int)) 1) ((as const (Array Int Int)) 0)) (abs b)) (* (mod a a) (* a a))))))
(check-sat)
