(set-logic ALL)
(set-info :status unsat)

(define-fun __cdiv ((x Int) (y Int)) Int (ite (>= x 0) (div x y) (- (div (- x) y))))

(declare-const a Int)
(declare-const b Int)
(declare-const s Int)
(declare-const r Int)

(assert (= (* a s) (+ (* b s) r)))
(assert (not (= s 0)))

(assert (not (= a (+ b (__cdiv r s)))))

(check-sat)
