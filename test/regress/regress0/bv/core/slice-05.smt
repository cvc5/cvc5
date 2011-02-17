(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x1 BitVec[64]))
  :extrafuns ((x2 BitVec[32]))
  :extrafuns ((x3 BitVec[16]))
  :extrafuns ((x4 BitVec[8]))
  :extrafuns ((x5 BitVec[4]))
  :extrafuns ((x6 BitVec[2]))
  :extrafuns ((x7 BitVec[1]))
  :assumption (= x1 (concat x2 x2))
  :assumption (= x2 (concat x3 x3))
  :assumption (= x3 (concat x4 x4))
  :assumption (= x4 (concat x5 x5))
  :assumption (= x5 (concat x6 x6))
  :assumption (= x6 (concat x7 x7))
  :formula (not (= (extract[63:63] x1) x7))
)
