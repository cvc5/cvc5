; COMMAND-LINE: --sygus-abduct --sygus-abort-size=2 
; EXPECT: (error "Maximum term size (2) for enumerative SyGuS exceeded.")
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 1

(set-logic QF_UFLIRA)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (>= n 1))
(assert (and (<= n x)(<= x (+ n 5))))
(assert (and (<= 1 y)(<= y m)))

(set-abduct-grammar

((Start Bool) (StartInt Int))
(
(Start Bool ((< StartInt StartInt)))
(StartInt Int (n m (+ StartInt StartInt) 0 1))
)
)

; With --sygus-abduct:
; Generate predicate(s) A that are consistent with the above axioms (i.e.
; their conjunction is SAT), and is such that the conjunction of the above
; axioms, A and the conjecture below are UNSAT.
; The signature of A is above grammar.
(check-sat-assuming ((< x y)))
