(set-logic HO_ALL)

(set-info :status sat)

(declare-fun Departments () (Table Int String))
(declare-fun Students () (Table Int String Int))
(declare-fun DepartmentStudents () (Table Int String Int String Int))

;(define-fun Departments () (Bag (Tuple Int String))
;  (bag.union_disjoint
;   (bag (tuple 1 "Computer") 1)
;   (bag (tuple 2 "Engineering") 1)))

;(define-fun Students () (Bag (Tuple Int String Int))
;  (bag.union_disjoint
;   (bag (tuple 1 "A" 1) 1)
;   (bag (tuple 2 "B" 1) 1)
;   (bag (tuple 3 "C" 2) 1)))

(assert
 (= DepartmentStudents
    (bag.union_disjoint (bag (tuple 1 "Computer" 1 "A" 1) 1)
                        (bag (tuple 1 "Computer" 2 "B" 1) 1)
                        (bag (tuple 2 "Engineering" 3 "C" 2) 1))))

(assert (= DepartmentStudents ((_ table.join 0 2) Departments Students)))

(check-sat)
