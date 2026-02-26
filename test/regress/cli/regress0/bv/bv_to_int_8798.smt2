; COMMAND-LINE: --solve-bv-as-int=iand
; EXPECT: 
; SCRUBBER: grep -v "uninterpreted"
; EXIT: 1
(set-logic ALL)
(declare-sort byte 0)
(declare-fun to_rep1 (byte) (_ BitVec 8))
(assert (forall ((a (Array Int byte))) (exists ((temp Int)) (= (to_rep1 (select a temp)) (to_rep1 (select a (+ temp 1)))))))
(check-sat)
