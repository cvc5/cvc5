(set-logic NRA)
(set-info :status unsat)
(declare-fun c () Real)
(declare-fun t () Real)
(assert (forall ((s Real)) (and (> t 0) (= 0 (* t c)) (or (< s c) (> s 1.0)))))
; previously answered "sat" with --nl-ext=none --nl-rlv=always
(check-sat)
