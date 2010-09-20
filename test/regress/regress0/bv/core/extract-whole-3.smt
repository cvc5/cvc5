(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (concat (concat (concat (concat (concat (concat bv0[1] bv1[1]) bv0[1]) bv1[1]) bv0[1]) bv1[1]) x) (concat bv21[6] x)))
)
