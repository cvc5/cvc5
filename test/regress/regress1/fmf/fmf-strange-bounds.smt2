; COMMAND-LINE: --fmf-bound --finite-model-find
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-sort U 0)
(declare-fun P (Int Int U) Bool)

(declare-fun S () (Set Int))

(declare-fun f (Int) U)
(declare-fun g (Int) U)

(declare-fun h (U) Int)

(assert (set.member 77 S))
(assert (>= (h (f 77)) 3))
(assert (>= (h (g 77)) 2))
(assert (not (= (g 77) (f 77))))

(assert (forall ((x Int) (z U)) (=> 
(or (= z (f x)) (= z (g x)))
(=> (set.member x S)
(P x 0 z)))))

(assert (forall ((x Int) (y Int) (z U)) (=>
(or (= x 5) (= x 6))
(=> (and (<= 0 y) (<= y x))
(P x y z)))))



(declare-fun Q (U Int) Bool)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(assert (distinct a b c))
(assert (forall ((x U) (y Int)) (=> (and (<= 3 y) (<= y 10) (or (= x c) (= x (f y)))) (Q x y))))
(assert (not (Q b 6)))

(check-sat)
