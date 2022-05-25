; COMMAND-LINE: --finite-model-find --sort-inference
; EXPECT: sat
(set-logic UFLIRA)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int) Int)
(assert (forall ((x Int)) (or (= (f x) (h x)) (= (f x) (g x)))))
(assert (not (= (f 3) (h 3))))
(assert (not (= (f 5) (g 5))))
(assert (= (f 4) (g 8)))

(check-sat)
