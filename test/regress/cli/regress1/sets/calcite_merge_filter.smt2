; REQUIRES: unrestricted-mode
; testMergeFilter, 
; q1: SELECT t.NAME FROM (SELECT * FROM DEPT AS DEPT WHERE DEPT.DEPTNO = 10) AS
;     t WHERE t.DEPTNO = 11
; q2: SELECT DEPT0.NAME FROM DEPT AS DEPT0 WHERE DEPT0.DEPTNO = 10
;
; Two filters merged into one, over projections of a relation.
; Before the projection and map composition rewrites this timed out.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const DEPT (Set (Tuple (Nullable Int) (Nullable String))))
(declare-const p0 (-> (Tuple (Nullable Int) (Nullable String)) Bool))
(declare-const q1 (Set (Tuple (Nullable String))))
(declare-const p1 (-> (Tuple (Nullable Int) (Nullable String)) Bool))
(declare-const q2 (Set (Tuple (Nullable String))))
(declare-const p2 (-> (Tuple (Nullable Int) (Nullable String)) Bool))
(assert (not (= q1 q2)))
(assert (= p0 (lambda ((t (Tuple (Nullable Int) (Nullable String)))) (and (nullable.is_some (nullable.lift (lambda ((BOUND_VARIABLE_393 Int) (BOUND_VARIABLE_394 Int)) (= BOUND_VARIABLE_393 BOUND_VARIABLE_394)) ((_ tuple.select 0) t) (nullable.some 10))) (nullable.val (nullable.lift (lambda ((BOUND_VARIABLE_393 Int) (BOUND_VARIABLE_394 Int)) (= BOUND_VARIABLE_393 BOUND_VARIABLE_394)) ((_ tuple.select 0) t) (nullable.some 10)))))))
(assert (= p1 (lambda ((t (Tuple (Nullable Int) (Nullable String)))) (and (nullable.is_some (nullable.lift (lambda ((BOUND_VARIABLE_431 Int) (BOUND_VARIABLE_432 Int)) (= BOUND_VARIABLE_431 BOUND_VARIABLE_432)) ((_ tuple.select 0) t) (nullable.some 11))) (nullable.val (nullable.lift (lambda ((BOUND_VARIABLE_431 Int) (BOUND_VARIABLE_432 Int)) (= BOUND_VARIABLE_431 BOUND_VARIABLE_432)) ((_ tuple.select 0) t) (nullable.some 11)))))))
(assert (= p2 (lambda ((t (Tuple (Nullable Int) (Nullable String)))) (and (nullable.is_some (nullable.lift (lambda ((BOUND_VARIABLE_461 Int) (BOUND_VARIABLE_462 Int)) (= BOUND_VARIABLE_461 BOUND_VARIABLE_462)) ((_ tuple.select 0) t) (nullable.some 10))) (nullable.val (nullable.lift (lambda ((BOUND_VARIABLE_461 Int) (BOUND_VARIABLE_462 Int)) (= BOUND_VARIABLE_461 BOUND_VARIABLE_462)) ((_ tuple.select 0) t) (nullable.some 10)))))))
(assert (= q1 ((_ rel.project 1) (set.filter p1 ((_ rel.project 0 1) (set.filter p0 DEPT))))))
(assert (= q2 ((_ rel.project 1) (set.filter p2 DEPT))))
(check-sat)
