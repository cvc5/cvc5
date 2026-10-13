; REQUIRES: unrestricted-mode
; COMMAND-LINE: --simplification=none
; COMMAND-LINE: --simplification=none --no-uf-lazy-ll
; EXPECT: unsat
(set-logic HO_ALL)
(declare-fun g (Int Int) Int)
(declare-fun P ((-> Int Int)) Bool)
(declare-fun h (Int) Int)
(declare-fun h2 (Int) Int)
; The lambda argument is lifted, while its occurrence in the equality stays
; inline. Congruence must relate both representations.
(assert (P (lambda ((x Int)) (g x x))))
(assert (not (P h)))
(assert (or (= h (lambda ((x Int)) (g x x))) (= h h2)))
(assert (not (= h h2)))
(check-sat)
