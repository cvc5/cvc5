(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :extrafuns ((y BitVec[32]))
  :formula
(not (= (extract[62:1] (concat x y)) (concat (extract[30:0] x) (extract[31:1] y))))
)
