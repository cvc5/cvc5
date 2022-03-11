; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :sets-ext true)
(declare-datatype Color ((Blue) (Purple)))
(declare-fun A () (Set Color))
(assert (> (set.card A) 1))
(check-sat)
(check-sat)
