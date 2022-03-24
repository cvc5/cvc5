(set-logic QF_NRAT)
(set-info :status unsat)
(set-option :arith-no-partial-fun true)
(declare-fun lat1 () Real)
(declare-fun lat2 () Real)

(declare-fun arctan2u () Real)
(define-fun arctan2 ((x Real) (y Real)) Real
  (arctan (/ y x)))
      
(assert (= (arctan2 lat1 lat2) 3))
(check-sat)
