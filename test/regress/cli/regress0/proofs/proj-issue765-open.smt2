; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental true)
(declare-const x Bool)
(declare-const x1 Bool)
(declare-const x2 Bool)
(assert (= x (and (or x (not x)) (or (not x) (ite x2 x1 false))) (and (or x (not x)) (or (not x) (ite x2 x1 false)))))
(push)
(assert (and false (= x (and (or x (not x)) (or (not x) (ite x2 x1 false))) (and (or x (not x)) (or (not x) (ite x2 x1 false))))))
(check-sat)
(pop)
(assert (not x2))
(check-sat)
