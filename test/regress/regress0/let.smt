(benchmark let_test
  :logic QF_UF
  :status unsat
  :extrafuns ((a U) (b U) (f U U)) 
  :formula (let (?x a) (not (= ?x a))))