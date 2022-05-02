(set-logic ALL)
(set-info :status unsat)
(declare-fun y () String)

(declare-fun x () String)

(assert
(= (str.++ (str.++ (str.++ y "B") "A") x) (str.++ (str.++ "A" x) "B")) 
)

; triggered an unsoundness during development of extended rewriter for strings, caught by sygus-rr-verify
(check-sat)
