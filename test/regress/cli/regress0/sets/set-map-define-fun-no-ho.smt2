; REQUIRES: unrestricted-mode
; COMMAND-LINE: --no-uf-ho-exp
; EXPECT: (error "Cannot handle assertion with term of kind set.map in this configuration.")
; EXIT: 1
(set-logic ALL)
(declare-fun g (Int) Int)
(declare-fun S () (Set Int))
(define-fun f ((x Int)) Int (g x))
(assert (not (= (set.map f S) (set.map g S))))
(check-sat)
