; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.contains (str.replace x y x) (str.substr y n 1)) (str.contains x (str.substr y n 1)))))
(check-sat)
