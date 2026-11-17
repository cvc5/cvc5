; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x String)
(assert (not (= (str.indexof (str.++ "aa" x "b") "b" 0) (+ (str.len "aa") (str.indexof (str.++ x "b") "b" 0)))))
(check-sat)
