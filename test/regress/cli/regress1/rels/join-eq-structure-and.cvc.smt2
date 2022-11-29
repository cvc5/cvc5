; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-datatypes ((unit 0)) (((u))))


(declare-fun w () (Relation Int unit))
(declare-fun z () (Relation unit Int))
(assert (let ((_let_1 (rel.join w z))) (let ((_let_2 (rel.join x y))) (and (= _let_2 _let_1) (= _let_2 (rel.transpose _let_1))))))
(assert (set.member (tuple 0 1) (rel.join x y)))
(declare-fun t () Int)
(assert (and (>= t 0) (<= t 1)))
(declare-fun s () Int)
(assert (and (>= s 0) (<= s 1)))
(assert (= (+ s t) 1))
(assert (set.member (tuple s u) w))
(assert (not (set.member (tuple u t) z)))
(check-sat)
