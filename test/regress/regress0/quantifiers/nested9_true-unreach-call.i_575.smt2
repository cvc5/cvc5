; COMMAND-LINE: --cbqi-bv
; EXPECT: unsat
(set-logic BV)
(set-info :status unsat)
(declare-fun c_main_~i~6 () (_ BitVec 32))
(declare-fun c_main_~j~6 () (_ BitVec 32))
(declare-fun c_main_~k~6 () (_ BitVec 32))
(assert
 (and (bvsle c_main_~i~6 (_ bv3 32)) (bvsle c_main_~i~6 (_ bv2 32))
 (exists ((v_nnf_34 (_ BitVec 32)))
  (and (bvsle (bvadd v_nnf_34 (_ bv3 32)) c_main_~k~6) 
  (bvsle v_nnf_34 (_ bv3 32)) (bvsle c_main_~j~6 (bvadd (bvmul (_ bv2 32) v_nnf_34) (_ bv1 32)))))))
(assert
 (not
 (and (bvsle c_main_~i~6 (_ bv3 32)) (bvsle c_main_~i~6 (_ bv2 32))
 (exists ((v_nnf_30 (_ BitVec 32)))
  (and (bvsle (bvadd v_nnf_30 (_ bv1 32)) c_main_~k~6) 
  (bvsle v_nnf_30 (_ bv3 32)) (bvsle c_main_~j~6 (bvadd (bvmul (_ bv2 32) v_nnf_30) (_ bv1 32))))))))
(check-sat)
(exit)

