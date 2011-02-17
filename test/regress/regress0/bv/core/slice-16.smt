(benchmark slice  
  :status sat
  :logic QF_BV
  :extrafuns ((x BitVec[16]))
  :assumption (= (extract[15:15] x) bv1[1])
  :assumption (= (extract[15:2] x) (extract[13:0] x))
  :formula (not (= x bv65535[16]))
)
