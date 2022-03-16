; EXPECT: (error "Cannot handle nested-recursive datatype ty0")
; EXIT: 1
(set-logic ALL)
(declare-datatype ty0 ((Emp) (Container (v2 (Set ty0)))))
(declare-fun v1 () ty0)
(assert (not ((_ is Emp) v1)))
(assert (= (v2 v1) (set.singleton v1)))
(check-sat)
