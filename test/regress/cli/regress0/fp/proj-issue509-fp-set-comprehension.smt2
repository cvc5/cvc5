; DISABLE-TESTER: lfsc
(set-logic ALL)
(set-option :sets-ext true)
(declare-datatype d ((c (s RoundingMode))))
(assert (set.member (set.choose (set.comprehension ((_x18 d)) false (s _x18))) (set.comprehension ((_x18 d)) false (s _x18))))
(set-info :status unsat)
(check-sat)
