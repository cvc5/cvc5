; COMMAND-LINE: --fmf-bound
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((list 0)) (((cons (head Int) (tail list)) (nil))))

(declare-fun P (Int) Bool)
(declare-fun S () (Set list))

; can use simple unification to infer bounds on x and y
(assert (forall ((x Int) (y list)) (=> (set.member (cons x y) S) (P x))))

(assert (set.member (cons 4 (cons 1 nil)) S))
(assert (set.member (cons 2 nil) S))

; should construct instantiation involving selectors for l 
(declare-fun l () list)
(assert ((_ is cons) l))
(assert (set.member l S))

; should not contribute to instantiations
(assert (set.member nil S))

(assert (not (P 1)))
(assert (not (P 0)))

(check-sat)
