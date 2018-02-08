; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)

(declare-sort Loc 0)

(declare-const w Loc)
(declare-const u1 Loc)
(declare-const u2 Loc)
(declare-const u3 Loc)
(declare-const nil Loc)

(declare-const w1 Loc)
(declare-const w2 Loc)
(declare-const w3 Loc)
(declare-const w4 Loc)

; allocated (not nil)
(assert (not (= w nil)))
(assert (not (= u1 nil)))
(assert (not (= u2 nil)))
(assert (not (= u3 nil)))
(assert (not (= w1 nil)))
(assert (not (= w2 nil)))
(assert (not (= w4 nil)))

; from model
;(assert (= w1 u3))
;(assert (= w2 u2))
;(assert (= w3 u1))
;(assert (= w4 u1))

(assert (sep (pto w u1) (pto u1 u2) (pto u2 u3) (pto u3 nil)))
(assert (and (sep (sep (pto w4 w1) (pto w1 w2) (pto w2 nil)) (pto w w3)) (sep (pto w w4) true)))

(check-sat)
