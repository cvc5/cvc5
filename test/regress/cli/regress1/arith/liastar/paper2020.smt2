
; REQUIRES: normaliz
(set-logic ALL)
(set-info :source "Solving Using LIA* Approximations
Maxwell Levatich, Nikolaj Bjorner, Ruzica Piskac, and Sharon Shoham
https://link.springer.com/chapter/10.1007/978-3-030-39322-9_17
")
(set-info :status unsat)
(set-option :dag-thresh 0)
(set-option :quiet true)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)

; nonnegative
(assert (>= x1 0)) 
(assert (>= x2 0)) 
(assert (>= x3 0))

; x1 ≠ x2 − 1 ∧ x3 = 1 ∧ (x1, x2, x3) ∈ {(m, L, s) | m = L − s ∧ s ≤ m}*
; x1 ≠ x2 − 1
(assert (distinct x1 (- x2 1))) 
; x3 = 1
(assert (= x3 1))

; (x1, x2, x3) ∈ {(m, L, s) | m = L − s ∧ s ≤ m}*
(assert 
  (int.star-contains 
    ((m Int) (L Int) (s Int)) 
    (and
      (= m (- L s))
      (<= s m))
    (tuple x1 x2 x3)))
(check-sat) 
