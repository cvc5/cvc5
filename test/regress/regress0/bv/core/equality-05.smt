(benchmark equality
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[1]))
  :extrafuns ((y BitVec[1]))
  :assumption (= x bv0[1])
  :assumption (= y bv1[1])
  :assumption (= x y)
  :formula
true
)
