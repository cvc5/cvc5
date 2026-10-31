; REQUIRES: normaliz
; A negated int.star-contains literal together with nonlinear multiplication.
; The liastar extension reduces the negated literal through a quantified
; lemma; the nonlinear extension must not count it as an unsatisfied
; assertion, which would make the result unknown. Here S = {2} and 3 is odd.
(set-logic HO_ALL)
(set-info :status sat)
(set-option :quiet true)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (not (int.star-contains (lambda ((x Int)) (= x 2)) a)))
(assert (= a 3))
(assert (= (* b c) 9))
(check-sat)
