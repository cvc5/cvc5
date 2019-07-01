; REQUIRES: dumping
; COMMAND-LINE: --dump raw-benchmark --preprocess-only
; SCRUBBER: grep assert
; EXPECT: (assert (let ((_let_1 (* x y))) (= _let_1 _let_1 _let_0)))
; EXPECT: (assert (let ((_let_1 (and a b))) (= _let_1 _let_1 (forall ((_let_0 Int)) (= 0 _let_0) ))))
; EXPECT: (assert (let ((_let_1 (and a b))) (= _let_1 _let_1 (forall ((x Int)) (forall ((y Int)) (let ((_let_2 (and b a))) (and _let_1 _let_2 _let_2 (= 0 _let_0))) ) ))))
(set-logic NIA)
(declare-const _let_0 Int)
(declare-const x Int)
(declare-const y Int)
(declare-const a Bool)
(declare-const b Bool)
(assert (= (* x y) (* x y) _let_0))
(assert (= (and a b) (and a b) (forall ((_let_0 Int)) (= 0 _let_0))))
(assert (= (and a b) (and a b) (forall ((x Int)) (forall ((y Int)) (and (and a b) (and b a) (and b a) (= 0 _let_0))))))
(check-sat)
