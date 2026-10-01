; REQUIRES: unrestricted-mode
; CPC checking fails on an instantiate step involving set.comprehension.
; DISABLE-TESTER: cpc
(set-logic ALL)
(set-option :sets-exp true)
(declare-datatype d ((c (s RoundingMode))))
(assert (set.member (set.choose (set.comprehension ((_x18 d)) false (s _x18))) (set.comprehension ((_x18 d)) false (s _x18))))
(set-info :status unsat)
(check-sat)
