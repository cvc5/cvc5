(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(let (?cvc_0 (extract[7:2] x)) (not (= (extract[5:0] ?cvc_0) ?cvc_0)))
)
