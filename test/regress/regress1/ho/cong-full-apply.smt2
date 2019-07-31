; COMMAND-LINE: --uf-ho
; EXPECT: unsat
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int) Int)

(assert (not (= (f 0) (g 0))))
(assert (not (= (f 0) (h 0))))
(assert (or (= f g) (= f h)))

(check-sat)
