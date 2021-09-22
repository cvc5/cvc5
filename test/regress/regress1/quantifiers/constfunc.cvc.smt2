; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(set-option :fmf-fun true)
(define-fun-rec f ((x Int)) Int 1)
(declare-fun x () Int)
(assert (not (= (f 7) x)))
(assert (= (f 8) x))
(check-sat)
