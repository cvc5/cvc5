; COMMAND-LINE: --learned-rewrite
; EXPECT: sat
(set-logic QF_UFNIA)
(declare-fun pow2 (Int) Int)
(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun ___ (Bool Int Int) Int)
(define-fun assertion_ltr () Bool (< (pow2 0) 0))
(assert (and (>= s (ite assertion_ltr (div (- s) (+ (___ (> k 0) k (- k)) 1)) (- 1))) (<= s (- (pow2 k) 1))))
(assert (< (pow2 0) 0))
(check-sat)
