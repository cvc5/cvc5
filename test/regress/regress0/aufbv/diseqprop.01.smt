(benchmark B_
  :status unsat
  :logic QF_AUFBV
  :extrafuns ((v6 BitVec[32]))
  :extrafuns ((v7 BitVec[32]))
  :extrafuns ((a1 Array[32:8]))
  :formula
 (and
(not (= (store a1 v6 bv0[8]) (store a1 v6 (extract[7:0] v7))))
(or (= v7 bv0[32]))
)
)
