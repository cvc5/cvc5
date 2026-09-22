; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)

(assert (not (= (str.len (str.++ "abcd" x "-" y "-" z "-" w "-" x "-" x "-" x "-" x "-")) (+ 4 (str.len x) 1 (str.len y) 1 (str.len z) 1 (str.len w) 1 (str.len x) 1 (str.len x) 1 (str.len x) 1 (str.len x) 1))))
(check-sat)
