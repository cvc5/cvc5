(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :extrafuns ((y BitVec[32]))
  :formula
(not (= (extract[60:3] (concat x y)) (concat (extract[28:0] x) (extract[31:3] y))))
)
