; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)

(assert (or
(not (= (str.contains (str.++ "A" x "B") (str.++ "C" y "D")) (str.contains x (str.++ "C" y "D"))))
(not (= (str.contains (str.++ "AC" x "B") (str.++ "C" y "D")) (str.contains (str.++ "C" x) (str.++ "C" y "D"))))
(not (= (str.contains (str.++ "A" x "B") (str.++ "C" y "B")) (str.contains (str.++ x "B") (str.++ "C" y "B"))))
(not (= (str.contains "ACEDB" (str.++ "C" y "D")) (str.contains "CED" (str.++ "C" y "D"))))

(not (= (str.indexof (str.++ x "ABCD") "C" 0) (str.indexof (str.++ x "ABC") "C" 0)))
(not (= (str.indexof (str.++ x "D") "C" 0) (str.indexof x "C" 0)))
(not (= (str.indexof (str.++ x "ABCD") (str.++ y "CC") 0) (str.indexof x (str.++ y "CC") 0)))

(not (= (str.indexof (str.++ x "ABCD") "CA" 0) (str.indexof (str.++ x "A") "CA" 0)))

))
(check-sat)
