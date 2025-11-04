; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-logic ALL)
(declare-datatype Color ((Red (x Int)) (Green) (Blue)))
(declare-const a Color)
(declare-fun P (Color) Bool)
(declare-fun Q (Int) Bool)
; should not require splitting on a, if (Q (x a)) is not asserted.
(assert (or (P a) (Q (x a))))
(check-sat)
