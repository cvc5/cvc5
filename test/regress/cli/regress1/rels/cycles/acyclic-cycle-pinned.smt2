; r is pinned to the 2-cycle {(a,b),(b,a)} with a != b.
; Asserting acyclicity of a cyclic relation is UNSAT. This is CORRECT.
(set-logic ALL)
(set-info :status unsat)
(set-option :rels-exp true)
(declare-sort A 0)
(declare-fun a () A)
(declare-fun b () A)
(declare-fun r () (Set (Tuple A A)))

(assert (distinct a b))
(assert (= r (set.insert (tuple a b) (set.singleton (tuple b a)))))
(assert (rel.acyclic (tuple r)))
(check-sat)
