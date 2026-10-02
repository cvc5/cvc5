; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic ALL)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(assert (set.member 1 A))
(assert (set.member 2 A))
(assert (set.member 1 B))
(assert (set.member 2 B))
(assert (not (= (set.choose A) (set.choose B))))
(assert (> (set.choose A) 1))
(check-sat)
