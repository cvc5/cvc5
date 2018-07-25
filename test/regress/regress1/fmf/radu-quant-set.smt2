; COMMAND-LINE: --fmf-bound
; EXPECT: unsat
(set-logic ALL_SUPPORTED)

(declare-const A (Set Int))
(declare-const B (Set Int))

(define-fun F () Bool
            (exists ((i Int) (j Int)) (and (distinct i j) (member i A) (member j B)))
)

(define-fun G () Bool
            (and (>= (card (union A B)) 2) (>= (card A) 1) (>= (card B) 1))
)

(assert (and G (not F)))

(check-sat)
