; COMMAND-LINE: --finite-model-find --decision=justification --uf-lazy-ll -q
; EXPECT: sat

(set-logic HO_ALL)
(declare-sort $$unsorted 0)
(declare-sort qML_mu 0)
(declare-sort qML_i 0)
(declare-fun scott_G (qML_mu qML_i) Bool)
(declare-fun scott_P ((-> qML_mu qML_i Bool) qML_i) Bool)

(assert
  (=
    scott_G
    (lambda ((X qML_mu) (__flatten_var_0 qML_i))
      (forall ((BOUND_VARIABLE_292 (-> qML_mu qML_i Bool)))
        (or
          (not (scott_P BOUND_VARIABLE_292 __flatten_var_0))
          (BOUND_VARIABLE_292 X __flatten_var_0)
          ) ))))

(assert
  (forall ((X_1 qML_i))
    (scott_P
      (lambda ((X qML_mu) (__flatten_var_0 qML_i))
        (forall ((BOUND_VARIABLE_292 (-> qML_mu qML_i Bool)))
          (or
            (not (scott_P BOUND_VARIABLE_292 __flatten_var_0))
            (BOUND_VARIABLE_292 X __flatten_var_0)) ))
      X_1
      )
    ))



(check-sat)
