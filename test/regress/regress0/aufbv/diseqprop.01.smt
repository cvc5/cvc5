(benchmark B_
  :status unsat
  :logic QF_AUFBV
  
  :extrafuns ((x BitVec[32]))
  :extrafuns ((y BitVec[32]))
  :extrafuns ((a Array[32:8]))
  
  :assumption (not (= (store a x bv0[8]) (store a x (extract[7:0] y))))
  :assumption (= y bv0[32])

  :formula true
)
