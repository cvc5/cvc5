(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[16]))
  :extrafuns ((y BitVec[12]))
  :assumption (= y (extract[11:0] x))
  :assumption (= y (extract[15:4] x))
  :assumption (= (extract[3:2] y) (extract[1:0] y))
  :assumption (= (extract[1:0] x) bv1[2])
  :formula (not (= x bv21845[16]))
)
