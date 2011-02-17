(benchmark slice
  :status unsat
  :logic QF_BV
  :extrafuns ((x BitVec[8]))
  :assumption (= x bv85[8])
  :formula (not (= (concat (concat (concat (extract[0:0] x) (extract[2:2] x)) (extract[4:4] x)) (extract[6:6] x)) bv15[4]))
)
