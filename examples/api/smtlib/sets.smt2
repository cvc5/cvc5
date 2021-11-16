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
      (set.inter (set.union A B) C)
      (set.union (set.inter A C) (set.inter B C)))
  )
)

; Verify emptset is a subset of any set
(check-sat-assuming
  (
    (not (set.subset (as set.empty (Set Int)) A))
  )
)

; Find an element in {1, 2} intersection {2, 3}, if there is one.
(check-sat-assuming
  (
    (set.member
      x
      (set.inter
        (set.union (set.singleton 1) (set.singleton 2))
        (set.union (set.singleton 2) (set.singleton 3))))
  )
)

(echo "A member: ")
(get-value (x))
