; COMMAND-LINE: --nl-cov
; EXPECT: sat
; REQUIRES: poly
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () (Array Int (Array Int Int)))
(assert (distinct b 0))
(assert (= 0 (+ (select (select c 0) (- a 8)) (select (select c 0) (mod (- 2 b) a)))))
(assert (distinct (select (select c 0) 0) (select (select c 0) (+ a (* 2 b)))))
(assert (distinct a 0))
(check-sat)
