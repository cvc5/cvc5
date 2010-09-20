(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (concat (concat (concat (concat (concat (concat x bv0[1]) bv1[1]) bv0[1]) bv1[1]) bv0[1]) bv1[1]) (concat x bv21[6])))
)
