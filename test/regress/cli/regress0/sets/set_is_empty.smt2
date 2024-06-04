; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun x () (Set Int))
(assert (set.member 0 x))
(assert (or (set.is_empty x) (set.is_empty (set.singleton 5))))
(check-sat)
