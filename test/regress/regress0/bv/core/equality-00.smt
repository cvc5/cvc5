(benchmark B_
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[32]))
  :extrafuns ((y BitVec[32]))
  :extrafuns ((z BitVec[32]))
  :assumption (= x y)
  :assumption (= y z)
  :formula (not (= x z))
)
