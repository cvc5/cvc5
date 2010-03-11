(benchmark euf_simp12.smt

  :status unsat
  :category { crafted }
  :logic QF_UF
  :extrasorts (A)
  :extrafuns ((x A))
  :extrafuns ((f A A))

  :formula (let (?cvc_0 (f (f x))) (let (?cvc_2 (f ?cvc_0)) (let (?cvc_3 (f ?cvc_2)) (let (?cvc_1 (f ?cvc_3)) (let (?cvc_4 (f ?cvc_1)) (not (implies (and (= ?cvc_4 ?cvc_0) (= ?cvc_1 ?cvc_2)) (and (= ?cvc_3 ?cvc_0) (= ?cvc_4 ?cvc_3)))))))))

)
