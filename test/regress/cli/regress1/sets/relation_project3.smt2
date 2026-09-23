; REQUIRES: unrestricted-mode
; DISABLE-TESTER: cpc
; Disabled since rel.project is not declared in the CPC signature. It
; survives into the proof, where the trusted steps below mention it.
; The same three rewrites for rel.project.
(set-logic HO_ALL)
(set-info :status unsat)

(declare-fun A () (Relation Int Int))
(declare-fun B () (Relation Int Int Int))

(assert (or
  (distinct ((_ rel.project 0 1) A) A)
  (distinct ((_ rel.project 0) ((_ rel.project 2 1) B)) ((_ rel.project 2) B))
  (distinct ((_ rel.project 1 0) (as set.empty (Relation Int Int))) (as set.empty (Relation Int Int)))))
(check-sat)
