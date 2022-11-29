(set-logic HO_ALL)

(set-info :status sat)

(declare-fun Departments () (Table Int String))
(declare-fun Students () (Table Int String Int))
(declare-fun DepartmentStudents () (Table Int String Int String Int))

(declare-fun d1 () (Tuple Int String))
(declare-fun d2 () (Tuple Int String))
(assert (distinct d1 d2))

(declare-fun s1 () (Tuple Int String Int))
(declare-fun s2 () (Tuple Int String Int))
(assert (distinct s1 s2))

(assert
  (distinct DepartmentStudents (as bag.empty (Table Int String Int String Int))))

(assert (bag.member d1 Departments))
(assert (bag.member d2 Departments))
(assert (bag.member s1 Students))
(assert (bag.member s2 Students))

(assert (= DepartmentStudents ((_ table.join 0 2) Departments Students)))

(check-sat)
