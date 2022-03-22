; SCRUBBER: grep -o "Symbol a is not declared"
; EXPECT: Symbol a is not declared
; EXIT: 1
(set-logic ALL)
(define-fun a () Bool false)
(reset-assertions)
(declare-const x Int)
(assert (and (= (+ x x) 0) true))
(assert a)
(check-sat)
