; COMMAND-LINE: --fmf-fun --no-check-models
; EXPECT: sat

(set-info :smt-lib-version 2.5)
(set-option :produce-models true)
(set-logic ALL)
(define-funs-rec (
(f11((va9 Int))Int)
(f3((v1f Int))Int)
)
( (f3 (ite (= 0 va9) (- 1) (div (- 1) va9)))
 (- (ite (= 0 v1f) 0 (mod 0 v1f))) 
))
(declare-fun v18d() Int)
(assert (= 0 (f11 v18d)))
(assert (= 22 v18d))
(check-sat)
