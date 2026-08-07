(set-logic ALL)
(set-info :status sat)
(set-option :rels-exp true)
; Test reflexive and reflexive transitive closure parsing

(declare-fun R1 () (Set (Tuple Int Int))) 
(declare-fun R2 () (Set (Tuple Int Int))) 

(assert (= R1 (rel.rclosure R2)))
(assert (= R1 (rel.rtclosure R2)))
(check-sat)