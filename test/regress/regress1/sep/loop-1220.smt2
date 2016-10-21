; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(set-info :status sat)

(declare-const x Int)
(declare-const a Int)

(declare-const y Int)
(declare-const b Int)
(declare-const y0 Int)
(declare-const b0 Int)
(declare-const y00 Int)
(declare-const b00 Int)

(assert (or false (sep (pto x a) (or false (sep (pto y b) (or false (sep (pto y0 b0) (pto y00 b00) )))))))
(assert (not (or false (sep (pto x a) (not (or false (sep (pto y b) (not (or false (sep (pto y0 b0) (not (pto y00 b00)) )))))))))) 

(check-sat)
