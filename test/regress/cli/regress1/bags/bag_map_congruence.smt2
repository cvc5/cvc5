; REQUIRES: tracing
; COMMAND-LINE: -t im
; SCRUBBER: grep -E '^\(lemma|^unsat$'
; EXPECT: unsat
; This is solved by congruence over bag.map in the equality engine, so the
; scrubber above checks that the bags solver generates no lemma at all.
(set-logic HO_ALL)
(define-fun f ((x Int)) Int (+ x 1))
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun C () (Bag Int))
(assert (or (= A B) (= A C)))
(assert (not (= (bag.map f A) (bag.map f B))))
(assert (not (= (bag.map f A) (bag.map f C))))
(check-sat)
