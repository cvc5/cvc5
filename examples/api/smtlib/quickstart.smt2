(set-logic ALL)
(set-option :produce-models true)
(set-option :incremental true)
; print unsat cores, include assertions in the unsat core that have not been named
(set-option :produce-unsat-cores true)
(set-option :dump-unsat-cores-full true)

; Declare real constants x,y
(declare-const x Real)
(declare-const y Real)

; Our constraints regarding x and y will be:
;
;   (1)  0 < x
;   (2)  0 < y
;   (3)  x + y < 1
;   (4)  x <= y

(assert (< 0 x))
(assert (< 0 y))
(assert (< (+ x y) 1))
(assert (<= x y))

(check-sat)
(echo "Values of declared real constants and of compound terms built with them.")
(get-value (x y (- x y)))

(echo "We will reset the solver with the (reset-assertions) command and check satisfiability of the same assertions but with the integers constants rather than with the real ones.")
(reset-assertions)
; Declare integer constants a,b
(declare-const a Int)
(declare-const b Int)
(assert (< 0 a))
(assert (< 0 b))
(assert (< (+ a b) 1))
(assert (<= a b))

(check-sat)
(get-unsat-core)
