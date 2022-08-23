; EXPECT: unknown
(set-logic ALL)
(set-option :sets-ext true)
(declare-const S (Set Float32))
(declare-const x Float32)
(assert (not (= x (set.choose (set.comprehension ((_x14 Float32)) false _x14)))))
(check-sat)
