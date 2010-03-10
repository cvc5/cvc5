(benchmark flet_test
  :logic QF_UF
  :status unsat
  :extrapreds ((a) (b)) 
  :formula (flet ($x (and a b)) (and $x (or (not a) (not b)))))