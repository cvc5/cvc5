; REQUIRES: tracing
; COMMAND-LINE: -t im
; SCRUBBER: grep -E '^\(lemma|^unsat$'
; EXPECT: unsat
; This is solved by congruence over rel.group in the equality engine, so the
; scrubber above checks that the sets solver generates no lemma at all.
(set-logic HO_ALL)
(declare-fun A () (Relation Int Int))
(declare-fun B () (Relation Int Int))
(declare-fun C () (Relation Int Int))
(assert (or (= A B) (= A C)))
(assert (not (= ((_ rel.group 0) A) ((_ rel.group 0) B))))
(assert (not (= ((_ rel.group 0) A) ((_ rel.group 0) C))))
(check-sat)
