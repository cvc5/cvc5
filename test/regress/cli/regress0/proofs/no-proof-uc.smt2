; DISABLE-TESTER: dump
; DISABLE-TESTER: proof
; COMMAND-LINE: --check-unsat-cores
; EXPECT: unsat
; EXPECT: (error "Cannot get a proof for this component when SAT solver is not proof producing.")
; EXIT: 1
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (<= 0 x))
(assert (<= 0 y))
(assert (< x 2))
(assert (< y 2))
(assert (not (< (* x y) 2)))
(check-sat)
(get-proof :sat)
