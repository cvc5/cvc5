; EXPECT: sat
(set-logic QF_BV)
(set-option :solve-bv-as-int sum)
(declare-const v8 Bool)
(declare-const bv_14-0 (_ BitVec 14))
(declare-const v12 Bool)
(assert (or (= ((_ repeat 5) (bvurem (_ bv77 7) (_ bv77 7))) ((_ repeat 5) (bvurem (_ bv77 7) (_ bv77 7)))) (= bv_14-0 bv_14-0 bv_14-0) (= ((_ repeat 5) (bvurem (_ bv77 7) (_ bv77 7))) ((_ repeat 5) (bvurem (_ bv77 7) (_ bv77 7)))) v12)) 
(assert (or v12 v8 v8 (= ((_ repeat 5) (bvurem (_ bv77 7) (_ bv77 7))) ((_ repeat 5) (bvurem (_ bv77 7) (_ bv77 7)))))) 
(check-sat)
