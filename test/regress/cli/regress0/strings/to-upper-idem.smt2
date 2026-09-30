; EXPECT: unsat
; Rewrite::STR_CONV_IDEM must have a complete proof, via RARE rule str-to-upper-idem.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.to_upper (str.to_upper s)) (str.to_upper s)))
(check-sat)
