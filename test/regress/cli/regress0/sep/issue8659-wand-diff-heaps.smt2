; DISABLE-TESTER: model
(set-logic ALL)
(set-info :status sat)

(declare-sort Loc 0)
(declare-heap (Loc Loc))

(declare-const x Loc)
(declare-const y Loc)

(assert (distinct x y))

(assert
  (sep
    (not (wand
      (pto x x)
      (not (pto x x))
    ))
    (pto x y)
  )
)

(check-sat)
