; REQUIRES: normaliz
; DISABLE-TESTER: proof
; The solution set x + y = 0 is a full line through the origin (negative
; coordinates included) and is closed under addition, so its star closure
; is the line itself: (3, -3) lies on it, (3, 2) does not.
(set-logic HO_ALL)
(set-option :incremental true)
(set-option :quiet true)
(declare-const a Int)
(declare-const b Int)

(set-info :status unsat)
(push 1)
(assert (= a 3))
(assert (= b 2))
(assert (int.star-contains (lambda ((x Int) (y Int)) (= (+ x y) 0)) a b))
(check-sat)
(pop 1)

(set-info :status sat)
(push 1)
(assert (= a 3))
(assert (= b (- 3)))
(assert (int.star-contains (lambda ((x Int) (y Int)) (= (+ x y) 0)) a b))
(check-sat)
(pop 1)
