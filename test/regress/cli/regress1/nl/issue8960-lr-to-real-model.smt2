; COMMAND-LINE: --learned-rewrite
; EXPECT: sat
(set-logic ALL)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)
(assert (distinct d 0))
(assert (distinct b 0))
(assert (= a (/ e d)))
(assert (distinct 1 (/ c 0)))
(assert (= 3 (/ a b b 0 0)))
(check-sat)
