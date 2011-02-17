(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[64]))
  :extrafuns ((y BitVec[32]))
  :extrafuns ((z BitVec[32]))
  :assumption (= x (concat y z))
  :formula (not (= (extract[31:0] x) z))
)
