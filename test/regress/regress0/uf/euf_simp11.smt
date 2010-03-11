(benchmark euf_simp11.smt

  :status unsat
  :difficulty { unknown }
  :category { crafted }
  :logic QF_UF
  :extrasorts (A)
  :extrafuns ((x A))
  :extrafuns ((f A A))






  :formula (let (?cvc_0 (f x)) (let (?cvc_2 (f ?cvc_0)) (let (?cvc_1 (f (f ?cvc_2))) (not (implies (and (= ?cvc_1 ?cvc_0) (= (f (f ?cvc_1)) ?cvc_0)) (= ?cvc_2 ?cvc_0))))))
)
