; REQUIRES: no-competition
; SCRUBBER: grep -o "Symbol 'a' not declared as a variable"
; EXPECT: Symbol 'a' not declared as a variable
; EXIT: 1
(set-logic ALL)
(define-fun a () Bool false)
(reset-assertions)
(declare-const x Int)
(assert (and (= (+ x x) 0) true))
(assert a)
(check-sat)
