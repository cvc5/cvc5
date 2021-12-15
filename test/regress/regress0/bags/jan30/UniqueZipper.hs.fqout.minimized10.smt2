(set-logic QF_ALL)
(set-info :status unsat)

; Observed
;
; sat as output instead of unsat
;
; What was going on?
;
; The solver was unable to reason that (bag.empty) cannot equal
; (bag 0). There were no membership predicates anywhere, just
; equalities.
;
; Fix
;
; Add the propagation rule: (true) => (>= (bag.count x (bag x))

(declare-fun z3f70 (Int) (Bag Int))
(declare-fun z3v85 () Int)
(declare-fun z3v86 () Int)
(declare-fun z3v87 () Int)
(declare-fun z3v90 () Int)

(assert (= (z3f70 z3v90) (bag.union_disjoint (z3f70 z3v85) (bag.union_disjoint (as bag.empty (Bag Int)) (bag z3v86 1)))))
(assert (= (z3f70 z3v90) (z3f70 z3v87)))
(assert (= (as bag.empty (Bag Int)) (z3f70 z3v87)))
(check-sat)
