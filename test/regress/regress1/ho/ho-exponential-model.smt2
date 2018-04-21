; COMMAND-LINE: --uf-ho
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)
(declare-fun f1 (Int Int Int Int) Int)
(declare-fun f2 (Int Int Int) Int)
(declare-fun f3 (Int Int) Int)
(declare-fun f4 (Int) Int)
(declare-fun f5 (Int Int Int) Int)
(declare-fun f6 (Int Int) Int)
(declare-fun f7 (Int) Int)


(assert (= (f1 0) (f1 1)))
(assert (= (f1 1) f2))

(assert (= (f2 0) (f2 1)))
(assert (= (f2 1) f3))

(assert (= (f3 0) (f3 1)))
(assert (= (f3 1) f4))

(assert (= (f4 0) (f4 1)))
(assert (= (f4 1) 2))


(assert (= (f1 3) (f1 4)))
(assert (= (f1 4) f5))

(assert (= (f5 3) (f5 4)))
(assert (= (f5 4) f6))

(assert (= (f6 3) (f6 4)))
(assert (= (f6 4) f7))

(assert (= (f7 3) (f7 4)))
(assert (= (f7 4) 5))

; this benchmark has a concise model representation for f1 if we use curried (tree-like) models for UF
(check-sat)
