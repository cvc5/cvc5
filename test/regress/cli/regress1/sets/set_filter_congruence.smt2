; REQUIRES: tracing
; COMMAND-LINE: -t im
; SCRUBBER: grep -E '^\(lemma|^unsat$'
; EXPECT: unsat
; This is solved by congruence over set.filter in the equality engine, so the
; scrubber above checks that the sets solver generates no lemma at all.
(set-logic HO_ALL)
(define-fun P ((x Int)) Bool (> x 0))
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun C () (Set Int))
(assert (or (= A B) (= A C)))
(assert (not (= (set.filter P A) (set.filter P B))))
(assert (not (= (set.filter P A) (set.filter P C))))
(check-sat)
