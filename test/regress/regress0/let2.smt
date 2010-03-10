(benchmark let_test
  :logic QF_UF
  :status sat
  :extrafuns ((a U) (b U) (f U U)) 
  :formula (let (?x (f a)) (= ?x (f b))))