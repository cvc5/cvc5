; COMMAND-LINE: --nl-ext-flatten-mon
; EXPECT: unsat
(set-logic QF_NIA)
(set-option :simplification none)
(declare-const c Int)
(declare-const i Int)
(declare-const j Int)
(declare-const f Int)
(declare-const g Int)
(assert (= f (* c j)))
(assert (= g (* i j)))
(assert (not (= (* f i) (* c g))))
(check-sat)
