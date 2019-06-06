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

(get-abduct 

((Start Bool) (StartInt Int))
(
(Start Bool ((< StartInt StartInt)))
(StartInt Int (n m (+ StartInt StartInt) 0 1))
)
)

(check-sat-assuming ((< x y)))
