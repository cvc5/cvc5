(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)

; Observed
;
; sat as output instead of unsat
;
; What was going on?
;
; The solver was unable to reason that (emptyset) cannot equal
; (singleton 0). There were no membership predicates anywhere, just
; equalities.
;
; Fix
;
; Add the propagation rule: (true) => (member x (singleton x))

(declare-fun z3f70 (Int) (Set Int))
(declare-fun z3v85 () Int)
(declare-fun z3v86 () Int)
(declare-fun z3v87 () Int)
(declare-fun z3v90 () Int)

(assert (= (z3f70 z3v90) (union (z3f70 z3v85) (union (as emptyset (Set Int)) (singleton z3v86)))))
(assert (= (z3f70 z3v90) (z3f70 z3v87)))
(assert (= (as emptyset (Set Int)) (z3f70 z3v87)))
(check-sat)
