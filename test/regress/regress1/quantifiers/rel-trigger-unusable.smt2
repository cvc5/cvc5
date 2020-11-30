; COMMAND-LINE: --relational-triggers --full-saturate-quant
; EXPECT: unsat
(set-logic UFNIA)
(set-info :status unsat)

(declare-fun two_to_the (Int) Int)


;other definitions
(define-fun intmax ((k Int)) Int (- (two_to_the k) 1))
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (two_to_the k)))

;l and SC
(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (distinct (intadd k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool true)

;conditional inverse
(define-fun inv ((k Int) (s Int) (t Int)) Int (intnot k (intadd k s t)))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)

(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (SC k s t) (l k (inv k s t) s t)))
(define-fun assertion_ltr () Bool (not (left_to_right k s t)))

;range helpers (everything between 0 and 2^k)
(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (two_to_the k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

;original assertions
(assert (range_assumptions k s t))

(assert assertion_ltr)
(declare-fun dummy (Int) Bool)
(assert (dummy t))
(assert (forall ((x Int)) (! (=> (>= x 0) (and (dummy x) (distinct (- (two_to_the k) 1) (* 2 x)))) :pattern ((dummy x))) ))

; relational-triggers segfaulted this previous due to a quantified formula that only has a relational trigger, which is unusable
(check-sat)
