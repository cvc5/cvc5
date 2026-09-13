; REQUIRES: unrestricted-mode
; COMMAND-LINE: --decision=justification
; COMMAND-LINE: --decision=internal
; COMMAND-LINE: --sat-solver=minisat --decision=justification
; COMMAND-LINE: --sat-solver=minisat --decision=internal
; EXPECT: unsat
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (sep (pto 1 2) (pto 3 2)))
(assert (= (sep (not (pto 1 2)) true true) (pto 3 2)))
(check-sat)
