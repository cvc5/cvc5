; COMMAND-LINE: --check-proofs --proof-check=eager
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (and (or (= (* (* (- x (* x y)) (- z 1)) (* (- x (* x y)) (- z 1)))
(div (- (* z (- x)) 2) 2)) (= (* (* (- x (* x y)) (- z 1)) (* (- x (* x y))
(- z 1))) (div (- (* z (- x)) 2) 2)))))
(check-sat)