; COMMAND-LINE: --solve-bv-as-int=iand --mbqi
; EXPECT: sat
(set-logic UFBV)
(declare-fun x ((_ BitVec 4)) (_ BitVec 4))
(assert (exists ((y (_ BitVec 4))) (= (x y) (_ bv0 4))))
(check-sat)
