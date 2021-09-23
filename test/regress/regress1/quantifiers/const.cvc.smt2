; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(define-fun-rec five () Int 5)
(assert (= five 6))
(check-sat)
