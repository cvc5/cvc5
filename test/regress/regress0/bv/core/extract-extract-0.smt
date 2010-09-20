(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :formula
(let (?cvc_0 (extract[31:0] x)) (not (= (extract[31:0] ?cvc_0) ?cvc_0)))
)
