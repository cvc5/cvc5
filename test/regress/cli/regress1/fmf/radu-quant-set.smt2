; COMMAND-LINE: --fmf-bound
; EXPECT: unsat
(set-logic ALL)

(declare-const A (Set Int))
(declare-const B (Set Int))

(define-fun F () Bool
            (exists ((i Int) (j Int)) (and (distinct i j) (set.member i A) (set.member j B)))
)

(define-fun G () Bool
            (and (>= (set.card (set.union A B)) 2) (>= (set.card A) 1) (>= (set.card B) 1))
)

(assert (and G (not F)))

(check-sat)
