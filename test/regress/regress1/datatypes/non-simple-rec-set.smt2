; COMMAND-LINE: --dt-nested-rec
; EXPECT: unsat
(set-logic ALL)
(declare-datatype T
((Emp) (Container (s (Set T)) )
))
(declare-fun a () T)
(assert (not ((_ is Emp) a)))
(assert (= (s a) (singleton a)))
(check-sat)
