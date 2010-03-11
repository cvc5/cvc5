(benchmark euf_simp13.smt

  :status unsat
  :difficulty { unknown }
  :category { crafted }
  :logic QF_UF
  :extrasorts (A)
  :extrafuns ((x A))
  :extrafuns ((f A A))
  :formula
  (let (?cvc_6 (f x)) (let (?cvc_0 (f ?cvc_6)) (flet ($cvc_1 (= ?cvc_0 x)) (let (?cvc_2 (f ?cvc_0)) (flet ($cvc_3 (= ?cvc_2 x)) (let (?cvc_4 (f ?cvc_2)) (let (?cvc_5 (f ?cvc_4)) (not (implies (or (or (or (and $cvc_1 $cvc_3) (and $cvc_1 (= ?cvc_5 x))) (and $cvc_3 (= ?cvc_4 ?cvc_2))) (and $cvc_3 (= ?cvc_5 ?cvc_2))) (= ?cvc_6 x))))))))))
)
