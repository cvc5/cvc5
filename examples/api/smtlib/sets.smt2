(set-logic QF_UFLIAFS)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const A (Set Int))
(declare-const B (Set Int))
(declare-const C (Set Int))
(declare-const x Int)

; Verify union distributions over intersection
(check-sat-assuming
  (
    (distinct
      (intersection (union A B) C)
      (union (intersection A C) (intersection B C)))
  )
)

; Verify emptset is a subset of any set
(check-sat-assuming
  (
    (not (subset (as emptyset (Set Int)) A))
  )
)

; Find an element in {1, 2} intersection {2, 3}, if there is one.
(check-sat-assuming
  (
    (member
      x
      (intersection
        (union (singleton 1) (singleton 2))
        (union (singleton 2) (singleton 3))))
  )
)

(echo "A member: ")
(get-value (x))