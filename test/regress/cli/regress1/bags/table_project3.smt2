; REQUIRES: unrestricted-mode
; Rewrites for table.project:
;   ((_ table.project 0 1 ... n-1) A) = A
;   ((_ table.project j...) ((_ table.project i...) A)) = ((_ table.project i[j]...) A)
;   ((_ table.project i...) (as bag.empty T)) = (as bag.empty T')
; Without them each projection is reduced to a bag.map over a lambda and neither
; disequality below can be refuted.
(set-logic HO_ALL)
(set-info :status unsat)

(declare-fun A () (Table Int Int))
(declare-fun B () (Table Int Int Int))

(assert (or
  ; identity projection, and a projection of a projection
  (distinct ((_ table.project 1) ((_ table.project 0 1) A)) ((_ table.project 1) A))
  ; composition when the inner projection reorders and drops a column
  (distinct ((_ table.project 0) ((_ table.project 2 1) B)) ((_ table.project 2) B))
  ; projection of the empty table
  (distinct ((_ table.project 1 0) (as bag.empty (Table Int Int))) (as bag.empty (Table Int Int)))))
(check-sat)
