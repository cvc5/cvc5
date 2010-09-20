(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(not (= (concat (concat (concat (concat (concat (concat bv0[1] (extract[31:31] x)) (extract[30:20] x)) (extract[19:10] x)) (extract[9:1] x)) (extract[0:0] x)) bv0[1]) (concat (concat bv0[1] x) bv0[1])))
)
