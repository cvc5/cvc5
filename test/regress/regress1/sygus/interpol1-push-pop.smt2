; COMMAND-LINE: --produce-interpols=default --sygus-active-gen=enum --check-interpols
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic NIA)
(declare-fun x ( ) Int)
(declare-fun y ( ) Int)
(declare-fun z ( ) Int)
(push)
(assert (= (* 2 x) y))
(get-interpol A (distinct (+ (* 2 z) 1) y))
(pop)

(assert (= (* 2 y) x))
(get-interpol A (distinct (+ (* 2 z) 1) x))
