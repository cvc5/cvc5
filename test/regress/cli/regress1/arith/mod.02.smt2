; EXPECT: unsat
;; introduces mod_by_zero Skolem
; DISABLE-TESTER: alethe
(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-fun n () Int)

(assert (distinct n 0))
(assert (> (mod n n) 0))

(check-sat)
