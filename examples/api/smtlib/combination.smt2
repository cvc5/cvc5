(set-logic QF_UFLIRA)
(set-option :produce-models true)
(set-option :incremental true)

(declare-sort U 0)

(declare-const x U)
(declare-const y U)

(declare-fun f (U) Int)
(declare-fun p (Int) Bool)

; 0 <= f(x)
(assert (<= 0 (f x)))
; 0 <= f(y)
(assert (<= 0 (f y)))
; f(x) + f(y) <= 1
(assert (<= (+ (f x) (f y)) 1))
; not p(0)
(assert (not (p 0)))
; p(f(y))
(assert (p (f y)))

(echo "Prove x != y is entailed. UNSAT (of negation) == ENTAILED")
(check-sat-assuming ((not (distinct x y))))

(echo "Call checkSat to show that the assertions are satisfiable")
(check-sat)

(echo "Call (getValue (...)) on terms of interest")
(get-value ((f x) (f y) (+ (f x) (f y)) (p 0) (p (f y))))
