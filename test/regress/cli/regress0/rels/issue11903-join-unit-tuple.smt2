; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error:'
; EXPECT: (error "Parse Error:
; EXIT: 1
(set-logic ALL)
(declare-fun s () (Set UnitTuple))
; join requires non-nullary relations
(assert (rel.join s (as set.empty (Set UnitTuple))))
(check-sat)
