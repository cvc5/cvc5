; COMMAND-LINE: -i
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-const x1 (Array Bool (Array Bool Bool)))
(assert (distinct (select x1 false) (store (select x1 false) false true) (select x1 (select (select x1 false) x)) (select (store x1 false (select x1 (select (select x1 false) (select (select x1 false) x)))) (select (store (select x1 false) x (select (select x1 false) (select (select x1 false) x))) (>= (- 1.0) 0.0)))))
(check-sat)
(check-sat-assuming ((= (_ -zero 8 24) (ite (>= 0.0 (ite (= (select x1 true) (select x1 (select (select x1 true) false))) 0.0 1.0)) (_ -zero 8 24) (fp.neg (_ -zero 8 24))))))
