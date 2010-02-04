(benchmark simple_uf
  :logic QF_UF
  :status unsat
  :extrasorts (A B)
  :extrafuns ((f A B) (x A) (y A))
  :formula (not (implies (= x y) (= (f x) (f y))))
  :status unsat
)
