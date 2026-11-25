; REQUIRES: unrestricted-mode
; dt_split on (Nullable Int) lists nullable.null first, as cvc5 orders the
; constructors of Nullable
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () (Nullable Int))
(declare-fun y () (Nullable Int))
(assert (not (= x y)))
(assert (not (nullable.is_some x)))
(assert (not (nullable.is_some y)))
(check-sat)
