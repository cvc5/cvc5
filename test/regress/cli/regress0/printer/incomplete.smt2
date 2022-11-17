; COMMAND-LINE: -o incomplete
; EXPECT: (incomplete INCOMPLETE QUANTIFIERS)
; EXPECT: unknown
(set-logic ALL)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (= (f x) (* x (f (- x 1))))))
(check-sat)
