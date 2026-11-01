; REQUIRES: unrestricted-mode
; DISABLE-TESTER: model
; (the model check of a bag filtered by (nullable.val t) of a null t fails, as
; on main)
; MAP_FIXED_COLUMNS reads a filter as fixing columns only when its rows are
; tuples: (= (nullable.val t) 5) over a (Bag (Nullable Int)) fixes no column.
; The bags differ for a null t whose nullable.val is 5.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X (Bag (Nullable Int)))
(define-fun five ((t (Nullable Int))) Bool (= (nullable.val t) 5))
(assert (not (= (bag.map (lambda ((t (Nullable Int)))
                           (nullable.some (nullable.val t)))
                         (bag.filter five X))
                (bag.filter five X))))
(check-sat)
