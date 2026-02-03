; COMMAND-LINE: --solve-bv-as-int=iand
; EXPECT:
; SCRUBBER: grep -v "uninterpreted"
; EXIT: 1
(set-logic ALL)
(declare-fun b ((_ BitVec 1)) (_ BitVec 1))
(assert (forall ((x (_ BitVec 1))) (= (b x) (b (_ bv0 1)))))
(check-sat)
