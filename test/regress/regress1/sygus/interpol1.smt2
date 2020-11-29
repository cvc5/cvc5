; COMMAND-LINE: --produce-interpols=default --sygus-active-gen=enum --check-interpols
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic NIA)
(declare-fun x ( ) Int)
(declare-fun y ( ) Int)
(declare-fun z ( ) Int)
(assert (= (* 2 x) y))
(get-interpol A (distinct (+ (* 2 z) 1) y)

; the grammar for the interpol-to-synthesize
((Start Bool) (StartInt Int))
(
(Start Bool ((< StartInt StartInt)))
(StartInt Int 
(y (+ StartInt StartInt) (div StartInt StartInt) (mod StartInt StartInt) 0 1 2))
)

)
