; COMMAND-LINE: --finite-model-find -q
(set-logic HO_ALL)
(set-info :status sat)
(declare-sort $$unsorted 0)
(declare-sort tptp.nat 0)
(declare-fun tptp.ord_less_eq_nat (tptp.nat tptp.nat) Bool)
(assert (= (lambda ((Y3 tptp.nat) (__flatten_var_0 tptp.nat)) (@ (lambda ((Z2 tptp.nat)) (= Y3 Z2)) __flatten_var_0)) (lambda ((X4 tptp.nat) (__flatten_var_0 tptp.nat)) (@ (lambda ((Y4 tptp.nat)) (and (@ (@ tptp.ord_less_eq_nat X4) Y4) (@ (@ tptp.ord_less_eq_nat Y4) X4))) __flatten_var_0))))
(set-info :filename bug_freeVar_BDD_General_data_270)
(check-sat)
