; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.contains "ab" (str.substr x n 1)) (or (= "" (str.substr x n 1)) (= "a" (str.substr x n 1)) (= "b" (str.substr x n 1))))))
(check-sat)
