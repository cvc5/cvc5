(set-logic QF_ALL)
(set-info :status unsat)

; Observed
;
; sat as output instead of unsat
;
; What was going on?
;
; The solver was unable to reason that (set.empty) cannot equal
; (set.singleton 0). There were no membership predicates anywhere, just
; equalities.
;
; Fix
;
; Add the propagation rule: (true) => (set.member x (set.singleton x))

(declare-fun z3f70 (Int) (Set Int))
(declare-fun z3v85 () Int)
(declare-fun z3v86 () Int)
(declare-fun z3v87 () Int)
(declare-fun z3v90 () Int)

(assert (= (z3f70 z3v90) (set.union (z3f70 z3v85) (set.union (as set.empty (Set Int)) (set.singleton z3v86)))))
(assert (= (z3f70 z3v90) (z3f70 z3v87)))
(assert (= (as set.empty (Set Int)) (z3f70 z3v87)))
(check-sat)
