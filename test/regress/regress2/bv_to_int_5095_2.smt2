; EXPECT: sat
; COMMAND-LINE: --solve-bv-as-int=sum -q
(set-logic BV)
(declare-const bv_42-0 (_ BitVec 42))
(assert (exists ((q28 (_ BitVec 42))) (distinct (bvudiv bv_42-0 bv_42-0) q28)))
(check-sat)
