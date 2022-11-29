; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(set-option :check-proofs true)
(set-option :proof-check eager)
(set-option :incremental true)
(declare-const x (Set Bool))
(assert (set.member (set.subset x (set.choose (set.singleton (set.minus (set.singleton (set.choose x)) (set.inter x (set.singleton (set.choose x))))))) (set.inter x (set.singleton (set.choose x)))))
(assert (set.subset x (set.choose (set.singleton (set.minus (set.singleton (set.choose x)) (set.inter x (set.singleton (set.choose x))))))))
(check-sat)
(check-sat-assuming ((set.choose (set.singleton (set.choose x)))))
(check-sat)