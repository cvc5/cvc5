(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x1 BitVec[64]))
  :extrafuns ((x2 BitVec[64]))
  :extrafuns ((y BitVec[32]))
  :extrafuns ((z BitVec[32]))
  :assumption (= x1 (concat y z))
  :assumption (= (extract[63:32] x2) y)
  :assumption (= (extract[31:0] x2) z)
  :formula (not (= x1 x2))
)
