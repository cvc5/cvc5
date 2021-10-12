; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-datatypes ((unit 0)) (((u))))


(declare-fun w () (Set (Tuple Int unit)))
(declare-fun z () (Set (Tuple unit Int)))
(assert (= (join x y) (join w z)))
(assert (member (tuple 0 1) (join x y)))
(assert (member (tuple 0 u) w))
(declare-fun t () Int)
(assert (and (> t 0) (< t 2)))
(assert (not (member (tuple u t) z)))
(check-sat)
