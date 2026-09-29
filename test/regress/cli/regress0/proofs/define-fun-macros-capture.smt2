; DISABLE-TESTER: alethe
; COMMAND-LINE: --parse-define-fun-macros -q
; EXPECT: sat
(set-logic ALL)
; Each assertion is valid, but would be false if variables were captured when
; expanding definitions.
; Expanding (f y) must not capture y by the binder in the body of f.
(define-fun f ((x Int)) Bool (exists ((y Int)) (> y x)))
(assert (forall ((y Int)) (f y)))
; A formal argument must not be confused with a binder of the same name and
; sort in the body.
(define-fun g ((y Int)) Bool (exists ((y Int)) (> y 0)))
(assert (g (- 1)))
; Capture in nested definitions.
(define-fun h ((z Int)) Bool (forall ((y Int)) (f (+ y z))))
(assert (forall ((y Int)) (h y)))
(check-sat)
