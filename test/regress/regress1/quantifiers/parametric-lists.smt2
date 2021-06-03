; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((List 1)) ((par (T) ((cons (head T) (tail (List T))) (nil)))))
(declare-datatypes ((KV 0)) (((kv (key Int) (value Int)) (nilKV))))
(declare-fun mapper ((List Int)) (List KV))
(assert
  (forall
    ((input (List Int)))
     (ite
        (= input (as nil (List Int)))
        (= (as nil (List KV)) (mapper input))
        (= (cons (kv 0 (head input)) (mapper (tail input))) (mapper input))
     )
  )
)
(declare-fun reduce ((List KV)) Int)
(assert
  (forall
    ((inputk (List KV)))
    (ite
      (= inputk (as nil (List KV)))
      (= 0 (reduce inputk))
      (= (+ (value (head inputk)) (reduce (tail inputk))) (reduce inputk))
    )
  )
)
(declare-fun sum ((List Int)) Int)
(assert
  (forall
    ((input (List Int)))
    (ite
      (= input (as nil (List Int)))
      (= 0 (sum input))
      (= (+ (head input) (sum (tail input))) (sum input))
    )
  )
)
(assert
  (not (= (sum (cons 0 (as nil (List Int)))) (reduce (mapper (cons 0 (as nil (List Int)))))))
)
(check-sat)
