; EXPECT: unsat
(set-logic UFNIA)
(declare-fun pow2 (Int) Int)
(define-fun intmax ((k Int)) Int (- (pow2 k) 1))
(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (<= x (intmax k))))
(define-fun intudivtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (pow2 k) 1) (div a b) ))
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (pow2 b)) (pow2 k)))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (pow2 k)))
(define-fun pow2_base_cases () Bool (and (= (pow2 0) 1) (= (pow2 1) 2) (= (pow2 2) 4) (= (pow2 3) 8) ) )
;qf axioms
(define-fun pow2_ax () Bool pow2_base_cases)
(define-fun and_ax ((k Int)) Bool true)
(define-fun or_ax ((k Int)) Bool true)
(define-fun xor_ax ((k Int)) Bool true)
; helpers
(define-fun is_bv_width ((k Int)) Bool
 (and
  (> k 0)
  (and_ax k)
  (or_ax k)
  (xor_ax k)
 )
)
(define-fun is_bv_var ((k Int) (x Int)) Bool (in_range k x))
; problem start
(assert pow2_ax)
(assert (not (forall ((s Int) (t Int) (k Int))
  (=>
   (and (is_bv_var k s) (is_bv_var k t) (is_bv_width k))
   (= (intadd k t (intadd k s (intshl k s t))) (intadd k s (intadd k t (intshl k s t))))
  )
 )
))
(check-sat)
