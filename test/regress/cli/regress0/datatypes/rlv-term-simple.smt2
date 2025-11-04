; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-logic ALL)
(declare-datatype Color ((Red) (Green) (Blue)))
(declare-const a Color)
(declare-const b Color)
(declare-const c Color)
(declare-fun P (Color) Bool)
; should only require splitting on a
(assert (or (P a) (P b) (P c)))
(check-sat)
