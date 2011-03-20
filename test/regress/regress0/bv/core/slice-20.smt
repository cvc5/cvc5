(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x1 BitVec[4]))
  :extrafuns ((y1 BitVec[4]))
  :extrafuns ((x2 BitVec[2]))
  :extrafuns ((y2 BitVec[2]))
  :extrafuns ((x3 BitVec[1]))
  :extrafuns ((y3 BitVec[1]))
  :assumption (= x1 y1)
  :assumption (= x1 (concat x2 x2))
  :assumption (= x2 (concat x3 x3))
  :assumption (= y1 (concat y2 y2))
  :assumption (= y2 (concat y3 y3))
  :formula (not (= x3 y3))
)
