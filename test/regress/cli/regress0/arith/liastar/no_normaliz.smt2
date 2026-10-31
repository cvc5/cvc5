; REQUIRES: no-normaliz
; EXIT: 1
; EXPECT: (error "cvc5 can't solve int.star-contains constraints since it was not configured with --normaliz")
;
; int.star-contains is solved by the liastar extension, which needs Normaliz.
; A build without Normaliz must reject the predicate instead of ignoring it.
(set-logic HO_ALL)
(declare-const a Int)
(assert (int.star-contains (lambda ((x Int)) (= x 2)) a))
(check-sat)
