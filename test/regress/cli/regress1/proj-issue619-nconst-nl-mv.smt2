; EXPECT: unknown
; DISABLE-TESTER: lfsc
(set-logic ALL)
(set-option :sets-ext true)
(declare-sort u 0)
(declare-const x u)
(check-sat-assuming ((set.member (set.choose (set.comprehension ((_x3 Real)) (is_int (sec 25980915886)) (seq.unit x))) (set.comprehension ((_x3 Real)) true (seq.unit x)))))
