; REQUIRES: unrestricted-mode
; The proof prints ((_ tuple.project 2 0) t) as (tuple.project (@list 2 0) t),
; and the empty projection (tuple.project t) as (tuple.project @list.nil t).
; Safe mode is excluded since the rewrite eliminating tuple.project is trusted.
(set-logic ALL)
(set-info :status unsat)
(declare-fun t () (Tuple Int String Bool))
(declare-fun u () (Tuple Bool Int))
(declare-fun v () UnitTuple)
(assert (= u ((_ tuple.project 2 0) t)))
(assert (= v (tuple.project t)))
(assert (or (not (= ((_ tuple.select 1) u) ((_ tuple.select 0) t)))
            (not (= v tuple.unit))))
(check-sat)
