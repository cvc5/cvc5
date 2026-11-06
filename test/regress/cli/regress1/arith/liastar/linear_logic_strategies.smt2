; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --no-arith-liastar-lazy
;
; In a linear logic with uninterpreted functions, equalities between a
; variable and a constant belong to UF (term-based theory assignment), so
; the linear solver does not see them. The lazy strategy must still reduce
; literals of either polarity, across push and pop. Here S = {2, 7, 8}.
(set-logic HO_UFLIA)
(set-option :incremental true)
(declare-const a Int)
(declare-const b Int)
(define-fun L ((v Int)) Bool
  (int.star-contains
    (lambda ((x Int)) (or (= x 2) (and (>= x 7) (<= x 8)))) v))

; 5 is not in S*
(set-info :status unsat)
(push 1)
(assert (L a))
(assert (= a 5))
(check-sat)
(pop 1)

; 9 = 2 + 7
(set-info :status sat)
(push 1)
(assert (L a))
(assert (= a 9))
(check-sat)
(pop 1)

(set-info :status unsat)
(push 1)
(assert (not (L a)))
(assert (= a 9))
(check-sat)
(pop 1)

(set-info :status sat)
(push 1)
(assert (not (L a)))
(assert (= a 5))
(check-sat)
(pop 1)

; 3 is not the sum of two elements of S*, except 0 + 3, and 3 is not in S*
(set-info :status unsat)
(push 1)
(assert (L a))
(assert (L b))
(assert (= (+ a b) 3))
(assert (>= a 0))
(assert (>= b 0))
(check-sat)
(pop 1)
