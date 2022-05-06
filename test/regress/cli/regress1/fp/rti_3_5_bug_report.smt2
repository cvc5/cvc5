; DISABLE-TESTER: lfsc
; COMMAND-LINE: --fp-exp
; EXPECT: unsat

(set-logic FP)
(set-info :source |Written by Mathias Preiner for issue #2932|)
(set-info :smt-lib-version 2.6)
(set-info :category crafted)
(set-info :status unsat)

(define-sort FP () (_ FloatingPoint 3 5))
(declare-const t FP)
(assert
  (distinct
    (= t (fp.roundToIntegral RNA t))  
    (exists ((x FP)) (= (fp.roundToIntegral RNA x) t)) 
 )
)
(check-sat)
(exit)
