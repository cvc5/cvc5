; COMMAND-LINE: --fmf-bound
; EXPECT: sat
(set-logic ALL)
(declare-datatypes () ((list (cons (head Int) (tail list)) (nil))))

(declare-fun P (Int) Bool)
(declare-fun S () (Set list))

; can use simple unification to infer bounds on x and y
(assert (forall ((x Int) (y list)) (=> (member (cons x y) S) (P x))))

(assert (member (cons 4 (cons 1 nil)) S))
(assert (member (cons 2 nil) S))

; should construct instantiation involving selectors for l 
(declare-fun l () list)
(assert (is-cons l))
(assert (member l S))

; should not contribute to instantiations
(assert (member nil S))

(assert (not (P 1)))
(assert (not (P 0)))

(check-sat)
