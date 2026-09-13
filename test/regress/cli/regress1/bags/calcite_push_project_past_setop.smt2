; REQUIRES: unrestricted-mode
; testPushProjectPastSetOp, ;
; q1: SELECT t.SAL FROM (SELECT * FROM EMP AS EMP UNION ALL SELECT * FROM EMP AS EMP0) AS t
; q2: SELECT EMP1.SAL FROM EMP AS EMP1 UNION SELECT EMP2.SAL FROM EMP AS EMP2
;
; The identity projection ((_ table.project 0 1 ... 8) EMP) comes from SELECT *.
; Before the projection and map composition rewrites this timed out.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const EMP (Bag (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
(declare-const q1 (Bag (Tuple (Nullable Int))))
(declare-const q2 (Bag (Tuple (Nullable Int))))
(assert (not (= q1 q2)))
(assert (= q1 ((_ table.project 6) (bag.union_disjoint ((_ table.project 0 1 2 3 4 5 6 7 8) EMP) ((_ table.project 0 1 2 3 4 5 6 7 8) EMP)))))
(assert (= q2 (bag.setof (bag.union_disjoint ((_ table.project 6) EMP) ((_ table.project 6) EMP)))))
(check-sat)
