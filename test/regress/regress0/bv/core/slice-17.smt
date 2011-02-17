(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[16]))
  :extrafuns ((y BitVec[12]))
  :assumption (= y (extract[11:0] x))
  :assumption (= y (extract[15:4] x))
  :assumption (= (extract[3:1] y) (extract[2:0] y))
  :assumption (= (extract[0:0] x) bv1[1])
  :formula (not (= x bv65535[16]))
)
