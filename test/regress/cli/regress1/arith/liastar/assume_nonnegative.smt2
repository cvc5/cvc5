; REQUIRES: normaliz
; DISABLE-TESTER: proof
(set-logic HO_ALL)
(set-info :status unsat)
(set-option :quiet true)
; disabling option arith-liastar-assume-nonnegative changes the answer to sat
(set-option :arith-liastar-assume-nonnegative true)
(declare-const a Int)
(assert (= a (- 5)))
(assert (int.star-contains (lambda ((x Int)) (= x (- 1))) a))
(check-sat)
