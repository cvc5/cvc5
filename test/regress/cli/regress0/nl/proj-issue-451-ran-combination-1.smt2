; REQUIRES: poly
; EXPECT: sat
(set-option :global-declarations true)
(set-logic QF_NRA)
(set-option :produce-unsat-cores true)
(declare-const _x0 Real)
(check-sat-assuming ( (>= (/ _x0 _x0) (/ (/ 2079598914 691107) _x0)) (and (> (/ (/ (/ 2079598914 691107) _x0) _x0) _x0) (> (- _x0) _x0))))
