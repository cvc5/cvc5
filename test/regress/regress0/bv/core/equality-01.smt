(benchmark B_
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[32]))
  :extrafuns ((y BitVec[32]))
  :extrafuns ((z BitVec[32]))
  :extrafuns ((w BitVec[32]))
  :assumption (= x y)
  :assumption (= y z)
  :assumption (= z w)
  :formula (not (= x w))
)
