(benchmark euf_simp10.smt

  :status unsat
  :difficulty { unknown }
  :category { crafted }
  :logic QF_UF
  :extrasorts (A)
  :extrafuns ((x A))
  :extrafuns ((f A A))

  :formula (let (?cvc_0 (f x)) (let (?cvc_1 (f (f ?cvc_0))) (flet ($cvc_2 (= ?cvc_1 ?cvc_0)) (not (implies (and $cvc_2 (= (f (f ?cvc_1)) ?cvc_0)) $cvc_2)))))
)
