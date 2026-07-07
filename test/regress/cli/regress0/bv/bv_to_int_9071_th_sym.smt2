; COMMAND-LINE: --solve-bv-as-int=iand --mbqi
; EXPECT: sat
(set-logic UFBV)
(declare-fun x ((_ BitVec 1)) (_ BitVec 1))
(assert (exists ((y (_ BitVec 1))) (= (x (bvnot y)) (_ bv0 1))))
(check-sat)
