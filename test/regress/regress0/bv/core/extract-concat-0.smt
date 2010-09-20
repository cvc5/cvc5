(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :extrafuns ((y BitVec[32]))
  :formula
(not (= (extract[63:32] (concat x y)) (extract[31:0] x)))
)
