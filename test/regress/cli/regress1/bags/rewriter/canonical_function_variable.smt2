; REQUIRES: unrestricted-mode
; CANONICAL_VARIABLE renames the variable of a lambda that applies it, as f
; in (f 0): its alpha key reads the operator of (f 0) like its arguments, so
; renaming reaches a fixed point, and the two maps are one term
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const B (Bag (-> Int Int)))
(assert (not (= (bag.map (lambda ((f (-> Int Int))) (f 0)) B)
                (bag.map (lambda ((g (-> Int Int))) (g 0)) B))))
(check-sat)
