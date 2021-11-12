; COMMAND-LINE: --uf-lazy-ll
; EXPECT: sat
(set-logic HO_ALL)
(declare-fun g (Int) Int)
(declare-fun h (Int) Int)
(define-fun f ((x Int)) Int (ite (> x 0) (* 2 x) x))

(declare-fun a () Int)
(declare-fun b () Int)


(assert (or (= f g) (= f h)))

(assert (and (= (h a) 26) (= (g b) 26)))

(check-sat)
