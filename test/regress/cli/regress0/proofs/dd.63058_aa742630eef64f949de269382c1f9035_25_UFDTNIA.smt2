; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-const x3 Int)
(assert (not (or x (= 0 (mod (mod x3 3) 3)))))
(assert x)
(check-sat)
