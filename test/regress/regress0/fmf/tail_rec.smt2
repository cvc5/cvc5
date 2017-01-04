; COMMAND-LINE: --fmf-fun --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(declare-sort elem 0)
(declare-datatypes () ((list (Nil) (Cons (hd elem) (tl list)))))
(define-fun-rec f ((x list)) elem
  (ite (is-Nil x) (f x) (hd x))
)
(declare-fun t () elem)
(assert (= t (f Nil)))
(check-sat)
