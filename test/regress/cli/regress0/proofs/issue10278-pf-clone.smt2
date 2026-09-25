; COMMAND-LINE: --produce-proofs
; External proof checking is disabled because the repeated get-proof
; commands print multiple proofs to the same output stream.
; DISABLE-TESTER: dump
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: cpc
; DISABLE-TESTER: alethe
; REQUIRES: no-competition
; SCRUBBER: grep -o "unsat"
; EXPECT: unsat
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (<= 0 x))
(assert (<= 0 y))
(assert (< x 2))
(assert (< y 2))
(assert (not (< (* x y) 2)))
(check-sat)
(get-proof)
(get-proof)
