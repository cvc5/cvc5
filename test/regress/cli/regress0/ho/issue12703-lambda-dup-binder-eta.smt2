; The model is correct, but the debug model check cannot evaluate the
; disequality between f and a non-constant lambda that has f in its body.
; REQUIRES: unrestricted-mode
; DISABLE-TESTER: model
; EXPECT: sat
(set-logic HO_ALL)
(declare-fun f (Int Int) Int)
(assert (not (= f (lambda ((x Int) (x Int)) (f x x)))))
(check-sat)
