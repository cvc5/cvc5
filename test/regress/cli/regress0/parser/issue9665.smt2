; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error:'
; EXPECT: (error "Parse Error:
; EXIT: 1
(set-logic ALL)
(define-sort NaturalNumber () Int)
(declare-const n NaturalNumber)
(assert (and
    (< (* n (select (as const (Array Int Int)) 0)) 500) ;upper limit condition
                ;n is odd
    (or (= (mod n 2) 0) (= (mod n 7) 0))
))
(check-sat)
(exit)
