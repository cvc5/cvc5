; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --no-arith-liastar-lazy
;
; A negated literal needs the exact reduction: the lazy strategy enumerates
; the cells of the predicate until none is left, then sends the equivalence
; and the quantified lemma for the negation. The summands (1, -1) and
; (-1, 2) generate S* = {(m - n, 2n - m) | m, n >= 0}: (1, 1) is in S* with
; m = 3 and n = 2, (1, 0) with m = 2 and n = 1, while (2, -3) would need
; n = -1.
(set-logic HO_ALL)
(set-option :incremental true)
(declare-const a Int)
(declare-const b Int)
(define-fun L ((u Int) (v Int)) Bool
  (int.star-contains
    (lambda ((x Int) (y Int))
      (or (and (= x 1) (= y (- 1))) (and (= x (- 1)) (= y 2)))) u v))

(set-info :status sat)
(push 1)
(assert (L a b))
(assert (= a 1))
(assert (= b 1))
(check-sat)
(pop 1)

(set-info :status unsat)
(push 1)
(assert (not (L a b)))
(assert (= a 1))
(assert (= b 1))
(check-sat)
(pop 1)

; (1, 0): m - n = 1 and 2n - m = 0 give n = 1, m = 2
(set-info :status unsat)
(push 1)
(assert (not (L a b)))
(assert (= a 1))
(assert (= b 0))
(check-sat)
(pop 1)

; (2, -3): m - n = 2 and 2n - m = -3 give n = -1
(set-info :status sat)
(push 1)
(assert (not (L a b)))
(assert (= a 2))
(assert (= b (- 3)))
(check-sat)
(pop 1)
