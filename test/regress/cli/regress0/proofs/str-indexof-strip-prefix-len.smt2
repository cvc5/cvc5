; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(assert (or
  (not (= (str.indexof (str.++ "a" x) x 1) (+ 1 (str.indexof x x 0))))
  (not (= (str.indexof (str.++ "abc" x) x 2) (+ 2 (str.indexof (str.++ "c" x) x 0))))
  (not (= (str.indexof (str.++ x "a" y) y (+ (str.len x) 1)) (+ 1 (str.len x))))
  (not (= (str.indexof (str.++ x "abc" y) y (+ (str.len x) 2)) (+ 2 (str.len x) (str.indexof (str.++ "c" y) y 0))))))
(check-sat)
