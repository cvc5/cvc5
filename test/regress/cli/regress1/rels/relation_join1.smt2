(set-logic HO_ALL)

(set-info :status sat)

(declare-fun Departments () (Relation Int String))
(declare-fun Students () (Relation Int String Int))
(declare-fun DepartmentStudents () (Relation Int String Int String Int))

(declare-fun d1 () (Tuple Int String))
(declare-fun d2 () (Tuple Int String))
(assert (distinct d1 d2))

(declare-fun s1 () (Tuple Int String Int))
(declare-fun s2 () (Tuple Int String Int))
(assert (distinct s1 s2))

(assert
  (distinct DepartmentStudents (as set.empty (Relation Int String Int String Int))))

(assert (set.member d1 Departments))
(assert (set.member d2 Departments))
(assert (set.member s1 Students))
(assert (set.member s2 Students))

(assert (= DepartmentStudents ((_ rel.table_join 0 2) Departments Students)))

(check-sat)
