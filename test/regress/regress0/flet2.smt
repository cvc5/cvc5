(benchmark flet_test
  :logic QF_UF
  :status sat
  :extrapreds ((a) (b)) 
  :formula (flet ($x (and a b)) (and $x (or a b))))