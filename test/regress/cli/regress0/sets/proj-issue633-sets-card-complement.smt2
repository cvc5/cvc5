; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :sets-exp true)
(declare-const x Real)
(assert (set.member (* x (+ x 1.0)) (set.complement (set.singleton 0.0))))
(assert (or (set.member (seq.nth (seq.unit 0.0) (set.card (set.complement (set.singleton 0.0)))) (set.complement (set.singleton 0.0)))))
(check-sat)
