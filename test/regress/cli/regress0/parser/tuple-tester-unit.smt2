; EXPECT: (error "Parse Error: tuple-tester-unit.smt2:7.29: Bad syntax for (_ is X), X cannot be a tuple constructor.")
; EXIT: 1
; DISABLE-TESTER: dump
;; Testers of tuples are not supported, including that of the unit tuple.
(set-logic ALL)
(declare-const u UnitTuple)
(assert ((_ is tuple.unit) u))
(check-sat)
