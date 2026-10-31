; REQUIRES: normaliz
; DISABLE-TESTER: proof
;
; int.star-contains in a linear logic. The liastar extension is independent
; of non-linear arithmetic, so HO_UFLIA suffices: UF for the lambda and
; quantifiers for the negated query. Here S = {2}, so S* is the set of even
; nonnegative integers.
(set-logic HO_UFLIA)
(set-option :incremental true)
(declare-const a Int)

; 3 is odd
(set-info :status unsat)
(push 1)
(assert (int.star-contains (lambda ((x Int)) (= x 2)) a))
(assert (= a 3))
(check-sat)
(pop 1)

; a = 2 is the only element of S* in [1, 2]
(set-info :status sat)
(push 1)
(assert (int.star-contains (lambda ((x Int)) (= x 2)) a))
(assert (>= a 1))
(assert (<= a 2))
(check-sat)
(pop 1)

; 6 is in S*, so the negation is false
(set-info :status unsat)
(push 1)
(assert (not (int.star-contains (lambda ((x Int)) (= x 2)) a)))
(assert (= a 6))
(check-sat)
(pop 1)
