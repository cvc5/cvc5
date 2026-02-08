; REQUIRES: normaliz
(set-logic ALL)
(set-info :source "Decision Procedures for Multisets with Cardinality Constraints
by Ruzica Piskac and Viktor Kuncak
https://link.springer.com/chapter/10.1007/978-3-540-78163-9_20
")
(set-info :status unsat)
(set-option :dag-thresh 0)
(set-option :quiet true)
(declare-fun k1 () Int)
(declare-fun k2 () Int)
(declare-fun x1 () Int)
(declare-fun L () Int)
(declare-fun x () Int)
(declare-fun z1 () Int)
(declare-fun z2 () Int)

; non negative
(assert (>= k1 0)) 
(assert (>= k2 0)) 
(assert (>= x1 0)) 
(assert (>= L 0)) 
(assert (>= x 0)) 
(assert (>= z1 0)) 
(assert (>= z2 0)) 

; k1 ≠ k2 − 1 ∧ (k1, k2, 1, 0, 0) ∈ ∑ F(x1, L, x, z1, z2)

; k1 ≠ k2 − 1
(assert 
  (distinct k1 (- k2 1))) 

;(k1, k2, 1, 0, 0) ∈ ∑ F(x1, L, x, z1, z2)
(assert 
  (int.star-contains 
    ((x1 Int) (L Int) (x Int) (z1 Int) (z2 Int)) 
    (and 
      (= z1 
        (ite 
          (= x1 
            (ite (<= L x) 0 (- L x))) 0 1)) 
      (= z2 (ite (<= x L) 0 1))) (tuple k1 k2 1 0 0))) 
(check-sat) 
