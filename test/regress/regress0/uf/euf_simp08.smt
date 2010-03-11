(benchmark euf_simp8.smt

  :status unsat
  :difficulty { unknown }
  :category { crafted }
  :logic QF_UF
  :extrasorts (A)
  :extrafuns ((x A))
  :extrafuns ((f A A))

  :formula (let (?cvc_1 (f x)) (let (?cvc_0 (f (f ?cvc_1))) (not (implies (and (= ?cvc_0 x) (= (f (f ?cvc_0)) ?cvc_0)) (= ?cvc_1 x)))))

)
