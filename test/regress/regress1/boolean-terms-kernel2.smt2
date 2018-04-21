; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_ABV)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun a () (Array Bool (Array (_ BitVec 32) (_ BitVec 32))))
(declare-fun v2 () (_ BitVec 32))
(declare-fun r0 () (_ BitVec 32))
(declare-fun r1 () (_ BitVec 32))
(declare-fun l () (_ BitVec 32))
(declare-fun i () (_ BitVec 32))
(assert c)
(push 1)
(assert (not (=> false (not (= i (select (select a true) (bvsub (bvmul (bvsdiv v2 (_ bv2 32)) (bvadd (bvmul (_ bv2 32) l) (_ bv1 32))) (_ bv1 32))))))))
(check-sat)
(pop 1)
(assert (not (=> (= i (select (select a true) (bvsub (bvmul (bvsdiv v2 (_ bv2 32)) (bvadd (bvmul (_ bv2 32) l) (_ bv1 32))) (_ bv1 32)))) (not (= r1 (ite b i r0))))))
(check-sat)
