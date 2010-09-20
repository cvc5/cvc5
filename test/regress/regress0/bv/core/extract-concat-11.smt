(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :extrafuns ((y BitVec[32]))
  :formula
(not (= (extract[59:4] (concat x y)) (concat (extract[27:0] x) (extract[31:4] y))))
)
