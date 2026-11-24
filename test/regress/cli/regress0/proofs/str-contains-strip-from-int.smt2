; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.contains (str.++ x (str.from_int n)) "ab") (str.contains x "ab"))))
(check-sat)
