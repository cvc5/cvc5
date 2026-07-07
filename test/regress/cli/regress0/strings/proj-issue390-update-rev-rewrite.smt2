(set-logic QF_BVSLIRA)
(declare-const _x3 String)
(declare-const _x5 Real)
(assert (=
  (str.rev _x3)
  (str.at 
    (str.update (str.rev _x3) (ubv_to_int #b000000000000000000000000000000000001) (str.rev _x3))
    (ubv_to_int #b000000000000000000000000000000000001))))
(set-info :status sat)
(check-sat)
