; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-datatypes ((unit 0)) (((u))))


(declare-fun w () (Set (Tuple Int unit)))
(declare-fun z () (Set (Tuple unit Int)))
(assert (= (rel.join x y) (rel.join w z)))
(assert (set.member (tuple 0 1) (rel.join x y)))
(assert (set.member (tuple 0 u) w))
(declare-fun t () Int)
(assert (and (> t 0) (< t 2)))
(assert (not (set.member (tuple u t) z)))
(check-sat)
