; COMMAND-LINE: --fp-exp
; EXPECT: unsat

(set-logic QF_FP)
(set-info :source |Written by Andres Noetzli for issue #2183|)
(set-info :smt-lib-version 2.6)
(set-info :category crafted)
(set-info :status unsat)

(declare-fun r () (_ FloatingPoint 5 9))
(define-fun rr () (_ FloatingPoint 5 9) ((_ to_fp 5 9) RNA (fp #b1 #b00000 #b1111111110)))

; Let's work out this one out manually
; #b1111111110 is an significand of
;  11111111110, rounding positions (g for guard, s for sticky)
;  123456789gs
; so g = 1, s = 0 which is the tie break case
; RNA says tie break goes away from zero, so this is a round up
; incrementing the significand carries up so the true result should be
; (fp #b1 #b00001 #x00000000)

(assert (= (fp #b1 #b00000 #xff) rr))
(check-sat)
