; EXPECT: unsat
(set-logic ALL)
(declare-fun uri () String)
(assert (not
(= (str.contains (str.replace (str.substr (str.substr uri 10 (+ (- 10) (str.len uri))) 0 (+ 1 (str.indexof (str.substr uri 10 (+ (- 10) (str.len uri))) "+" 0))) "+" " ") "@") (or (str.contains (str.substr (str.substr uri 10 (+ (- 10) (str.len uri))) 0 (+ 1 (str.indexof (str.substr uri 10 (+ (- 10) (str.len uri))) "+" 0))) "@") (and (str.contains (str.substr (str.substr uri 10 (+ (- 10) (str.len uri))) 0 (+ 1 (str.indexof (str.substr uri 10 (+ (- 10) (str.len uri))) "+" 0))) "+") (str.contains " " "@"))))
))
(check-sat)
