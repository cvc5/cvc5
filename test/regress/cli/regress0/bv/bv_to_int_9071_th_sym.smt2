; EXPECT: 
; SCRUBBER: grep -v "quantified.variables"
; COMMAND-LINE: --solve-bv-as-int=iand
; EXIT: 1
(set-logic UFBV)
(declare-fun x ((_ BitVec 1)) (_ BitVec 1))
(assert (exists ((y (_ BitVec 1))) (= (x (bvnot y)) (_ bv0 1))))
(check-sat)
