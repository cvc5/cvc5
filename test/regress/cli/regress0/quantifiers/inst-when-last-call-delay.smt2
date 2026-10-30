; COMMAND-LINE: --inst-when=last-call-delay
; EXPECT: unsat
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (forall ((x Int)) (! (> (f x) (+ x 1)) :pattern ((f x)))))
(assert (or (< (f a) a) (< (f b) b)))
(assert (<= a b))
(check-sat)
