(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (extract[0:0] (extract[8:7] (extract[14:6] (extract[19:5] (extract[23:4] (extract[26:3] (extract[28:2] (extract[30:1] x)))))))) (extract[28:28] x)))
)
