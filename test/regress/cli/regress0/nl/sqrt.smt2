; COMMAND-LINE: -q
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
(set-option :incremental true)
(set-logic ALL)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(push)
(assert (= (sqrt 1.0) 1.0))
(check-sat)
(pop)

(push)
(assert (= (sqrt 1.0) (- 1.0)))
(check-sat)
(pop)

(push)
(assert (= x 1.0))
(assert (not (= (sqrt 1.0) (sqrt x))))
(check-sat)
(pop)

(push)
(assert (< x 0.0))
(assert (= (sqrt 1.0) (sqrt x)))
(check-sat)
(pop)

(push)
(assert (= (sqrt y) z))
(assert (= (sqrt x) (sqrt y)))
(assert (not (= (sqrt x) z)))
(check-sat)
(pop)
