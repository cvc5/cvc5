; COMMAND-LINE: --incremental --check-unsat-cores
; EXPECT: unsat
; EXPECT: unsat
(set-logic NRA)
(declare-const r0 Real)
(assert (! (forall ((q0 Bool) (q1 Real)) (= (* r0 r0) r0 r0)) :named IP_2))
(assert (! (not (forall ((q2 Real)) (not (<= 55.033442 r0 55.033442 q2)))) :named IP_5))
(push 1)
(check-sat)
(pop 1)
(check-sat)
