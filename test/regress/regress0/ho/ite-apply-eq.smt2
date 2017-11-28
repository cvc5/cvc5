; COMMAND-LINE: --uf-ho
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int) Int)

(assert (= h (ite (> x 0) f g)))

(assert (= (h 4) 5))

(check-sat)
