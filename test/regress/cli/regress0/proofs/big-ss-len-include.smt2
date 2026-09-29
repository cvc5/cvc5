; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)

(assert (not (= 
(str.substr (str.++ "abcd" x "-" y "-" z "-" w "-" x "-" x "-" x "-" x "-abc") 0 (+ 12 (* 5 (str.len x)) (str.len y) (str.len z) (str.len w)))
(str.++ "abcd" x "-" y "-" z "-" w "-" x "-" x "-" x "-" x "-"))))
(check-sat)
