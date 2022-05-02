; COMMAND-LINE: -i
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-const a String)
(declare-const b String)
(declare-const c String)
(push)
(assert (= (str.++ a b) c))
(assert (= a "A"))
(assert (= c ""))
(check-sat)
(pop)
(assert (= (str.++ a b) (str.++ "A" c)))
(assert (= c (str.++ a b)))
(check-sat)
