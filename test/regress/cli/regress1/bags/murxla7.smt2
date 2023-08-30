(set-logic ALL)
(set-info :status unsat)
(declare-sort s 0)
(declare-const x s)
(assert
(not
(seq.contains
    (seq.unit x)
    (seq.update
      (seq.unit x)
      (bag.card (bag.union_disjoint (bag x 28601551) (bag x 28601551)))
      (seq.unit x)))
))
(check-sat)
