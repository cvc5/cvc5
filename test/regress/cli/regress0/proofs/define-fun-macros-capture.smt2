; COMMAND-LINE: --proof-define-fun-macros
; Logos does not yet support the proof of this benchmark, independently of
; whether definitions are treated as macros.
; DISABLE-TESTER: cpc-logos
; EXPECT: unsat
(set-logic ALL)
(define-fun P ((y Int)) Bool (exists ((x Int)) (distinct x y)))
(assert (not (forall ((x Int)) (P x))))
(check-sat)
