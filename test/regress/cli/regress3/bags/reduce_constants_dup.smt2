; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: cpc
; DISABLE-TESTER: lfsc
; test name: testReduceConstantsDup2
;Translating sql query: SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 7 AND EMP.DEPTNO = 8 AND EMP.EMPNO = 10 AND EMP.MGR IS NULL AND EMP.EMPNO = 10
;Translating sql query: SELECT 10 AS EMPNO, t0.ENAME, t0.JOB, CAST(NULL AS INT) AS MGR, t0.HIREDATE, t0.SAL, t0.COMM, t0.DEPTNO, t0.SLACKER FROM (SELECT * FROM EMP WHERE FALSE) AS t0
(set-logic HO_ALL)
(set-info :status unsat)
(set-option :dag-thresh 0)
(set-option :uf-lazy-ll true)
(set-option :fmf-bound true)
(set-option :tlimit-per 10000)


(declare-const EMP (Bag (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
(declare-const q1 (Bag (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
(declare-const q2 (Bag (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
(declare-const p2 (-> (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)) Bool))
(declare-const p3 (-> (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)) Bool))
(declare-const nullableOr (-> (Nullable Bool) (Nullable Bool) (Nullable Bool)))
(declare-const nullableAnd (-> (Nullable Bool) (Nullable Bool) (Nullable Bool)))
(declare-const f4 (-> (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)) (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int))))
(assert (= nullableAnd (lambda ((x (Nullable Bool)) (y (Nullable Bool))) (ite (and (nullable.is_null x) (= y (nullable.some false))) (nullable.some false) (ite (and (= x (nullable.some false)) (nullable.is_null y)) (nullable.some false) (ite (and (nullable.is_null x) (= y (nullable.some true))) (as nullable.null (Nullable Bool)) (ite (and (= x (nullable.some true)) (nullable.is_null y)) (as nullable.null (Nullable Bool)) (nullable.some (and (nullable.val x) (nullable.val y))))))))))
(assert (= nullableOr (lambda ((x (Nullable Bool)) (y (Nullable Bool))) (ite (and (nullable.is_null x) (= y (nullable.some true))) (nullable.some true) (ite (and (= x (nullable.some true)) (nullable.is_null y)) (nullable.some true) (ite (and (nullable.is_null x) (= y (nullable.some false))) (as nullable.null (Nullable Bool)) (ite (and (= x (nullable.some false)) (nullable.is_null y)) (as nullable.null (Nullable Bool)) (nullable.some (or (nullable.val x) (nullable.val y))))))))))
(assert (= p2 (lambda ((t (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)))) (and (nullable.is_some (nullableAnd (nullableAnd (nullableAnd (nullableAnd (nullable.lift (lambda ((BOUND_VARIABLE_549341 Int) (BOUND_VARIABLE_549342 Int)) (= BOUND_VARIABLE_549341 BOUND_VARIABLE_549342)) ((_ tuple.select 7) t) (nullable.some 7)) (nullable.lift (lambda ((BOUND_VARIABLE_549347 Int) (BOUND_VARIABLE_549348 Int)) (= BOUND_VARIABLE_549347 BOUND_VARIABLE_549348)) ((_ tuple.select 7) t) (nullable.some 8))) (nullable.lift (lambda ((BOUND_VARIABLE_549354 Int) (BOUND_VARIABLE_549355 Int)) (= BOUND_VARIABLE_549354 BOUND_VARIABLE_549355)) ((_ tuple.select 0) t) (nullable.some 10))) (nullable.some (nullable.is_null ((_ tuple.select 3) t)))) (nullable.lift (lambda ((BOUND_VARIABLE_549363 Int) (BOUND_VARIABLE_549364 Int)) (= BOUND_VARIABLE_549363 BOUND_VARIABLE_549364)) ((_ tuple.select 0) t) (nullable.some 10)))) (nullable.val (nullableAnd (nullableAnd (nullableAnd (nullableAnd (nullable.lift (lambda ((BOUND_VARIABLE_549341 Int) (BOUND_VARIABLE_549342 Int)) (= BOUND_VARIABLE_549341 BOUND_VARIABLE_549342)) ((_ tuple.select 7) t) (nullable.some 7)) (nullable.lift (lambda ((BOUND_VARIABLE_549347 Int) (BOUND_VARIABLE_549348 Int)) (= BOUND_VARIABLE_549347 BOUND_VARIABLE_549348)) ((_ tuple.select 7) t) (nullable.some 8))) (nullable.lift (lambda ((BOUND_VARIABLE_549354 Int) (BOUND_VARIABLE_549355 Int)) (= BOUND_VARIABLE_549354 BOUND_VARIABLE_549355)) ((_ tuple.select 0) t) (nullable.some 10))) (nullable.some (nullable.is_null ((_ tuple.select 3) t)))) (nullable.lift (lambda ((BOUND_VARIABLE_549363 Int) (BOUND_VARIABLE_549364 Int)) (= BOUND_VARIABLE_549363 BOUND_VARIABLE_549364)) ((_ tuple.select 0) t) (nullable.some 10))))))))
(assert (= p3 (lambda ((t (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)))) (and (nullable.is_some (nullable.some false)) (nullable.val (nullable.some false))))))
(assert (not (= q1 q2)))
(assert (= (nullable.val (as nullable.null (Nullable Bool))) false))
(assert (= f4 (lambda ((t (Tuple (Nullable Int) (Nullable String) (Nullable String) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int) (Nullable Int)))) (tuple (nullable.some 10) ((_ tuple.select 1) t) ((_ tuple.select 2) t) (as nullable.null (Nullable Int)) ((_ tuple.select 4) t) ((_ tuple.select 6) t) ((_ tuple.select 5) t) ((_ tuple.select 7) t) ((_ tuple.select 8) t)))))
(assert (= q1 ((_ table.project 0 1 2 3 4 5 6 7 8) (bag.filter p2 EMP))))
(assert (= q2 (bag.map f4 (bag.filter p3 EMP))))
(check-sat)
