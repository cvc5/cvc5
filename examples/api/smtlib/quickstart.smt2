;! [docs-smt2-quickstart-1 start]
(set-logic ALL)
;! [docs-smt2-quickstart-1 end]
;! [docs-smt2-quickstart-2 start]
(set-option :produce-models true)
(set-option :incremental true)
; print unsat cores, include assertions in the unsat core that have not been named
(set-option :produce-unsat-cores true)
(set-option :dump-unsat-cores-full true)
;! [docs-smt2-quickstart-2 end]

;! [docs-smt2-quickstart-3 start]
; Declare real constants x,y
(declare-const x Real)
(declare-const y Real)
;! [docs-smt2-quickstart-3 end]

;! [docs-smt2-quickstart-4 start]
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
;! [docs-smt2-quickstart-4 end]

;! [docs-smt2-quickstart-5 start]
(check-sat)
;! [docs-smt2-quickstart-5 end]
;! [docs-smt2-quickstart-6 start]
(echo "Values of declared real constants and of compound terms built with them.")
(get-value (x y (- x y)))
;! [docs-smt2-quickstart-6 end]

;! [docs-smt2-quickstart-7 start]
(echo "We will reset the solver with the (reset-assertions) command and check satisfiability of the same assertions but with the integers constants rather than with the real ones.")
(reset-assertions)
; Declare integer constants a,b
(declare-const a Int)
(declare-const b Int)
;! [docs-smt2-quickstart-7 end]
;! [docs-smt2-quickstart-8 start]
(assert (< 0 a))
(assert (< 0 b))
(assert (< (+ a b) 1))
(assert (<= a b))
;! [docs-smt2-quickstart-8 end]

;! [docs-smt2-quickstart-9 start]
(check-sat)
;! [docs-smt2-quickstart-9 end]
;! [docs-smt2-quickstart-10 start]
(get-unsat-core)
;! [docs-smt2-quickstart-10 end]
