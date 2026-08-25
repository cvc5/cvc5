; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

; Regression for a transitive-closure graph bug in TheorySetsRels::check().
; An unguarded call to buildTCGraphForRel rebuilt the internal TC graph from the
; base relation's members only, overwriting the closure memberships that
; applyTCRule had already added for the same relation. As a result doTCInference
; never chained the closure edge below and the solver diverged instead of
; reporting unsat.

(declare-fun x () (Relation Int Int))

; base edge: (2,3) in x, hence (2,3) in (rel.tclosure x)
(assert (set.member (tuple 2 3) x))

; closure edge not derivable from x alone: (1,2) in (rel.tclosure x)
(assert (set.member (tuple 1 2) (rel.tclosure x)))

; transitivity of (1,2) and (2,3) forces (1,3) in (rel.tclosure x),
; which contradicts the following assertion
(assert (not (set.member (tuple 1 3) (rel.tclosure x))))

(check-sat)
