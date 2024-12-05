; EXPECT: unsat
;; Unsat core checking with proofs at one point had issues for
;; this benchmark due to cycle detection in LazyCDProofChain
(set-logic ALL)
(set-option :incremental false)
(set-option :fmf-fun true)
(declare-fun x () Int)
(define-fun-rec fact ((x Int)) Int (ite (> x 0) (* x (fact (- x 1))) 1))
(assert (= (fact 0) 2))
(assert (= x (fact 3)))
(check-sat)
